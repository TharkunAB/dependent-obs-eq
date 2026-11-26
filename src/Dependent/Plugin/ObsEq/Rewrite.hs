{-# LANGUAGE LambdaCase #-}

-- |
-- Module      : Dependent.Plugin.ObsEq.Rewrite
-- Description : Constructive Knuth-Bendix completion over Given equalities
-- License     : BSD-3-Clause
-- Maintainer  : mpg@mpg.is
--
-- Proof-producing ground variable elimination and unfailing Knuth-Bendix
-- completion over in-scope @[G]@ nominal equalities and reachable certified
-- closed type-family axioms. Every rewrite step constructs a verified System FC
-- nominal 'CoercionN' without 'UnivCo'.
module Dependent.Plugin.ObsEq.Rewrite
  ( KBEnv
  , buildKBEnv
  , normalizeTypeKB
  , proveGoalConstructively
  ) where

import Control.Applicative ( (<|>) )
import Control.Monad ( foldM, guard )
import Data.List ( nubBy, permutations )
import qualified Data.Map.Strict as Map
import Data.Maybe ( fromMaybe, isJust )
import qualified Data.Set as Set
import Data.Word ( Word64 )
import Numeric.Natural ( Natural )

import GHC.Core.Coercion.Axiom
  ( BranchIndex
  , Branched
  , CoAxBranch
  , CoAxiom
  , CoAxiomRule (BranchedAxiom)
  , closedTyFamCoAxiom_maybe
  , coAxBranchCoVars
  , coAxBranchLHS
  , coAxBranchRHS
  , coAxBranchTyVars
  , coAxiomBranches
  , coAxiomNthBranch
  , fromBranches
  )
import GHC.Core.FamInstEnv ( apartnessCheck )
import GHC.Core.Predicate ( EqRel (NomEq), Pred (ClassPred, EqPred), classifyPredType )
import GHC.Core.TyCo.Rep ( TyLit, Type (..) )
import qualified GHC.Data.List.Infinite as Inf
import GHC.Data.Pair ( Pair (..) )
import GHC.Plugins hiding ( (<>) )
import GHC.Types.Unique ( getKey )
import GHC.Tc.Types.Constraint ( Ct, ctEvCoercion, ctEvidence, ctPred )
import GHC.Tc.Utils.TcType ( tcEqType )

{- Note [Constructive KBO completion without UnivCo]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Before invoking bytecode property testing, the solver runs a two-phase algebraic
normalizer over in-scope Given nominal equalities and certified closed
type-family axioms:

1. Phase 1 (Triangular variable unification and constructor decomposition):
   Eliminates unconstrained variables @[G] v ~# rhs@ where @v@ does not occur in
   @rhs@ (orienting variable-variable equalities strictly by @Unique@ to prevent
   two-cycle oscillation) and decomposes generative constructor equalities
   @'Con a_1 .. a_k ~# 'Con b_1 .. b_k@ via 'SelTyCon'. Eliminating GADT
   refinement variables first ensures that @[G] n ~# 'Succ k@ substitutes
   @'Succ k@ for @n@ instead of rewriting @'Succ k@ back to @n@.

2. Phase 2 (Bounded unfailing Knuth-Bendix completion):
   Translates remaining homogeneous Given equations and reachable single-sort
   closed type-family branches into 'KBTerm's, runs bounded unfailing completion
   (@fuel = 128@, @maxNodes = 64@) under a context-closed Knuth-Bendix order
   ('kboCompareGround'), and tracks an explicit 'ProofRecipe' ('PrGiven',
   'PrAxiom', 'PrSel', 'PrSym', 'PrTrans', 'PrCong') for every derived rule.

When left and right goal endpoints normalize to syntactically identical types,
'proveGoalConstructively' returns a pure System FC 'CoercionN' with zero
'UnivCo's. Even under 'RefuteOnly' and 'ExplicitOnly', bare nominal goals are
soundly discharged when constructively entailed.
-}

-- | Head symbol of a homogeneous first-order type application.
data KBHead
  = KHCon !TyCon ![Type]
  | KHTermApp !Id
  | KHApp
  | KHLit !TyLit

instance Eq KBHead where
  KHCon tc1 ps1 == KHCon tc2 ps2 =
    tc1 == tc2 && length ps1 == length ps2 && and (zipWith tcEqType ps1 ps2)
  KHTermApp f1 == KHTermApp f2 = f1 == f2
  KHApp == KHApp = True
  KHLit l1 == KHLit l2 = l1 == l2
  _ == _ = False

type UKey = Word64

uKey :: Uniquable a => a -> UKey
uKey = getKey . getUnique

-- | First-order representation of homogeneous GHC 'Type' trees.
data KBTerm
  = KBVar !UKey !Kind
  | KBRigid !(Maybe UKey) !Type
  | KBNode !KBHead ![KBTerm] !Type

instance Eq KBTerm where
  KBVar u1 _ == KBVar u2 _ = u1 == u2
  KBRigid u1 t1 == KBRigid u2 t2 = u1 == u2 && t1 `tcEqType` t2
  KBNode h1 as1 _ == KBNode h2 as2 _ =
    h1 == h2 && length as1 == length as2 && and (zipWith (==) as1 as2)
  _ == _ = False

kbTermType :: KBTerm -> Type
kbTermType (KBVar _ k) = k
kbTermType (KBRigid _ ty) = ty
kbTermType (KBNode _ _ ty) = ty

kbNodeCount :: KBTerm -> Int
kbNodeCount (KBNode _ as _) = 1 + sum (map kbNodeCount as)
kbNodeCount _ = 1

kbWeight :: KBTerm -> Natural
kbWeight (KBNode _ as _) = 1 + sum (map kbWeight as)
kbWeight _ = 1

-- | Constructive coercion recipe producing a homogeneous nominal 'CoercionN'.
data ProofRecipe
  = PrRefl !Type
  | PrGiven !CoercionN
  | PrAxiom !(CoAxiom Branched) !BranchIndex ![TyVar] ![KBTerm] !Type
  | PrSel !Int !ProofRecipe
  | PrSym !ProofRecipe
  | PrTrans !ProofRecipe !ProofRecipe
  | PrCong !KBHead ![ProofRecipe]
  | PrSubst !(Map.Map UKey KBTerm) !ProofRecipe

data KBRule = KBRule
  { krLhs :: !KBTerm
  , krRhs :: !KBTerm
  , krProof :: !ProofRecipe
  , krIsAxiom :: !Bool
  }

data VarRewrite = VarRewrite
  { vrVar :: !Var
  , vrTarget :: !Type
  , vrCo :: !CoercionN
  }

-- | Completed algebraic rewriting environment for one solver pass.
data KBEnv = KBEnv
  { kbeVarMap :: !(UniqFM Var VarRewrite)
  , kbeOriented :: ![KBRule]
  , kbeUnoriented :: ![KBRule]
  }

-- | Build a 'KBEnv' from in-scope Given constraints and Wanted goal types.
buildKBEnv :: [Ct] -> [Type] -> KBEnv
buildKBEnv givens goalTys =
  let rawEqs = extractNominalGivens givens
      (varRewrites, residualEqs) = solveTriangularVars rawEqs
      varMap = listToUFM [(vrVar r, r) | r <- varRewrites]
      substResiduals =
        [ (lhs', rhs', mkTransCo (mkSymCo coL) (mkTransCo co (coR)))
        | (lhs, rhs, co) <- residualEqs
        , let (lhs', coL) = applyVarSubst varMap lhs
        , let (rhs', coR) = applyVarSubst varMap rhs
        , not (lhs' `tcEqType` rhs')
        ]
      givenRules0 = concatMap seedGroundEquation substResiduals
      seedTys = goalTys ++ concat [[l, r] | (l, r, _) <- substResiduals]
      axiomRules = if null substResiduals then [] else collectReachableAxiomRules seedTys
      (oriented0, unoriented0) = partitionRules (givenRules0 ++ axiomRules)
      (orientedFinal, unorientedFinal) =
        if null givenRules0
          then (oriented0, unoriented0)
          else completeKB 128 64 oriented0 unoriented0 givenRules0
   in KBEnv
        { kbeVarMap = varMap
        , kbeOriented = orientedFinal
        , kbeUnoriented = unorientedFinal
        }

-- | Normalize a 'Type' under 'KBEnv', returning @(normTy, co, usedGivenCos)@
-- where @co :: ty ~#N normTy@ contains zero 'UnivCo's.
normalizeTypeKB :: KBEnv -> Type -> (Type, CoercionN, [Coercion])
normalizeTypeKB env ty0 =
  let (ty1, co1) = applyVarSubst (kbeVarMap env) ty0
      (ty2, co2) =
        if null (kbeOriented env) && null (kbeUnoriented env)
          then (ty1, mkNomReflCo ty1)
          else normalizeGroundKB env 32 ty1
      fullCo = mkCheckedTrans ty0 ty2 (mkTransCo co1 co2)
      usedCos = [mkCoVarCo cv | cv <- nonDetEltsUniqSet (coVarsOfCo fullCo)]
   in (ty2, fullCo, usedCos)

-- | Attempt to prove @lhs ~#N rhs@ purely constructively from 'KBEnv'.
proveGoalConstructively :: KBEnv -> Type -> Type -> Maybe CoercionN
proveGoalConstructively env lhs rhs = do
  let (nfL, coL, _) = normalizeTypeKB env lhs
      (nfR, coR, _) = normalizeTypeKB env rhs
  guard (nfL `tcEqType` nfR)
  let cand = mkTransCo coL (mkSymCo coR)
      Pair kL kR = coercionKind cand
  guard (kL `tcEqType` lhs && kR `tcEqType` rhs)
  pure cand

mkCheckedTrans :: Type -> Type -> CoercionN -> CoercionN
mkCheckedTrans expectedL expectedR co =
  let Pair actualL actualR = coercionKind co
   in if actualL `tcEqType` expectedL && actualR `tcEqType` expectedR
        then co
        else mkNomReflCo expectedL

-- ---------------------------------------------------------------------------
-- Phase 1: Triangular Variable Elimination & Constructor Decomposition
-- ---------------------------------------------------------------------------

extractNominalGivens :: [Ct] -> [(Type, Type, CoercionN)]
extractNominalGivens = concatMap extractOne
  where
    extractOne ct =
      let co = ctEvCoercion (ctEvidence ct)
       in case classifyPredType (ctPred ct) of
            EqPred NomEq lhs rhs
              | typeKind lhs `tcEqType` typeKind rhs ->
                  [(lhs, rhs, co)]
            ClassPred cls args
              | getOccString cls `elem` ["~", "~~"]
              , rhs : lhs : _ <- reverse args
              , typeKind lhs `tcEqType` typeKind rhs ->
                  let selCo = mkSelCo (SelTyCon (length args - 1) Nominal) co
                      Pair l r = coercionKind selCo
                   in [(lhs, rhs, selCo) | l `tcEqType` lhs && r `tcEqType` rhs]
            _ -> []

solveTriangularVars :: [(Type, Type, CoercionN)] -> ([VarRewrite], [(Type, Type, CoercionN)])
solveTriangularVars eqs0 = go 32 emptyUFM [] eqs0
  where
    go :: Int -> UniqFM Var VarRewrite -> [(Type, Type, CoercionN)] -> [(Type, Type, CoercionN)] -> ([VarRewrite], [(Type, Type, CoercionN)])
    go 0 subst residuals rest = (nonDetEltsUFM subst, reverse residuals ++ rest)
    go _ subst residuals [] = (nonDetEltsUFM subst, reverse residuals)
    go fuel subst residuals ((lhs0, rhs0, co0) : queue) =
      let (lhs, coL) = applyVarSubst subst lhs0
          (rhs, coR) = applyVarSubst subst rhs0
          co = mkTransCo (mkSymCo coL) (mkTransCo co0 coR)
       in if lhs `tcEqType` rhs
            then go (fuel - 1) subst residuals queue
            else case orientVarEq lhs rhs co of
              Just vr ->
                let single = unitUFM (vrVar vr) vr
                    subst' =
                      mapUFM
                        ( \old ->
                            let (t', c') = applyVarSubst single (vrTarget old)
                             in old {vrTarget = t', vrCo = mkTransCo (vrCo old) c'}
                        )
                        subst
                    subst'' = addToUFM subst' (vrVar vr) vr
                 in go (fuel - 1) subst'' [] (reverse residuals ++ queue)
              Nothing ->
                case decomposeInjEq lhs rhs co of
                  Just subEqs -> go (fuel - 1) subst residuals (subEqs ++ queue)
                  Nothing -> go fuel subst ((lhs, rhs, co) : residuals) queue

orientVarEq :: Type -> Type -> CoercionN -> Maybe VarRewrite
orientVarEq lhs rhs co =
  case (extractPlainVar lhs, extractPlainVar rhs) of
    (Just v1, Just v2)
      | uKey v1 == uKey v2 -> Nothing
      | uKey v1 > uKey v2
      , varKindOrType v1 `tcEqType` typeKind rhs ->
          Just (VarRewrite v1 rhs co)
      | varKindOrType v2 `tcEqType` typeKind lhs ->
          Just (VarRewrite v2 lhs (mkSymCo co))
    (Just v1, Nothing)
      | not (occursInType v1 rhs)
      , varKindOrType v1 `tcEqType` typeKind rhs ->
          Just (VarRewrite v1 rhs co)
    (Nothing, Just v2)
      | not (occursInType v2 lhs)
      , varKindOrType v2 `tcEqType` typeKind lhs ->
          Just (VarRewrite v2 lhs (mkSymCo co))
    _ -> Nothing
  where
    extractPlainVar ty =
      case coreFullView ty of
        TermVarTy v -> Just v
        TyVarTy tv -> Just tv
        _ -> Nothing

    varKindOrType v = if isTyVar v then tyVarKind v else varType v

nominalRolesPrefix :: Int -> TyCon -> [Role]
nominalRolesPrefix n tc = take n (Inf.toList (tyConRolesX Nominal tc))

decomposeInjEq :: Type -> Type -> CoercionN -> Maybe [(Type, Type, CoercionN)]
decomposeInjEq lhs rhs co
  | Just (tc1, args1) <- splitTyConApp_maybe (coreFullView lhs)
  , Just (tc2, args2) <- splitTyConApp_maybe (coreFullView rhs)
  , tc1 == tc2
  , length args1 == length args2
  , isGenerativeTyCon tc1 Nominal =
      let roles = nominalRolesPrefix (length args1) tc1
          nDep = homSplitIndex tc1 (length args1)
          (dep1, hom1) = splitAt nDep args1
          (dep2, hom2) = splitAt nDep args2
       in if and (zipWith tcEqType dep1 dep2)
            then
              Just
                [ (a1, a2, mkSelCo (SelTyCon idx Nominal) co)
                | (idx, r, a1, a2) <- zip4 [nDep ..] (drop nDep roles) hom1 hom2
                , r == Nominal
                , typeKind a1 `tcEqType` typeKind a2
                ]
            else Nothing
  | otherwise = Nothing
  where
    zip4 (w : ws) (x : xs) (y : ys) (z : zs) = (w, x, y, z) : zip4 ws xs ys zs
    zip4 _ _ _ _ = []

occursInType :: Var -> Type -> Bool
occursInType target = go
  where
    u = getUnique target
    go ty =
      case coreFullView ty of
        TermVarTy v -> getUnique v == u || go (varType v)
        TermAppTy f arg -> getUnique f == u || go (varType f) || go arg
        TyVarTy tv -> getUnique tv == u || go (tyVarKind tv)
        TyConApp _ args -> any go args
        AppTy f a -> go f || go a
        FunTy _ ma mult a r -> go ma || go mult || go a || go r
        ForAllTy ma b r ->
          go ma
            || go (varType (binderVar b))
            || (getUnique (binderVar b) /= u && go r)
        CastTy t kco -> go t || (target `elemVarSet` coVarsOfCo kco)
        ClassAppTy s i d x k -> getUnique s == u || go i || go d || go x || go k
        DepFunTy _ b r -> go (varType b) || (getUnique b /= u && go r)
        DepDictTy b r -> go (varType b) || (getUnique b /= u && go r)
        ExistsTy _ tv r -> go (tyVarKind tv) || (getUnique tv /= u && go r)
        _ -> False

-- | Apply triangular variable rewrites across all 'Type' constructors,
-- including 'TermAppTy' and 'CastTy', building a homogeneous 'CoercionN'.
applyVarSubst :: UniqFM Var VarRewrite -> Type -> (Type, CoercionN)
applyVarSubst varMap
  | isNullUFM varMap = \ty -> (ty, mkNomReflCo ty)
  | otherwise = go
  where
    go ty =
      case coreFullView ty of
        TermVarTy v
          | Just vr <- lookupUFM varMap v
          , varType v `tcEqType` typeKind (vrTarget vr) ->
              (vrTarget vr, vrCo vr)
        TyVarTy tv
          | Just vr <- lookupUFM varMap tv
          , tyVarKind tv `tcEqType` typeKind (vrTarget vr) ->
              (vrTarget vr, vrCo vr)
        TermAppTy f arg
          | isJust (splitFunTy_maybe (varType f)) ->
              let (arg', coArg) = go arg
               in if isReflCo coArg
                    then (ty, mkNomReflCo ty)
                    else (TermAppTy f arg', mkTermAppCo f coArg)
        TyConApp tc args ->
          let nDep = homSplitIndex tc (length args)
              roles = nominalRolesPrefix (length args) tc
              (depArgs, homArgs) = splitAt nDep args
              homRoles = drop nDep roles
           in if all (== Nominal) homRoles
                then
                  let (homArgs', homCos) = unzip (map go homArgs)
                   in if all isReflCo homCos
                        then (ty, mkNomReflCo ty)
                        else
                          let ty' = mkTyConApp tc (depArgs ++ homArgs')
                              co' = mkTyConAppCo Nominal tc (map mkNomReflCo depArgs ++ homCos)
                           in (ty', mkCheckedTrans ty ty' co')
                else (ty, mkNomReflCo ty)
        AppTy f a
          | isJust (splitFunTy_maybe (typeKind f)) ->
              let (f', coF) = go f
                  (a', coA) = go a
               in if isReflCo coF && isReflCo coA
                    then (ty, mkNomReflCo ty)
                    else
                      let ty' = mkAppTy f' a'
                          co' = mkAppCo coF coA
                       in (ty', mkCheckedTrans ty ty' co')
        CastTy inner kco ->
          let (inner', coInner) = go inner
           in if isReflCo coInner
                then (ty, mkNomReflCo ty)
                else
                  if isReflCo kco
                    then (inner', mkCheckedTrans ty inner' coInner)
                    else
                      let ty' = mkCastTy inner' kco
                          cLeft = mkSymCo (mkGReflRightCo Nominal inner kco)
                          cRight = mkGReflRightCo Nominal inner' kco
                          co' = mkTransCo cLeft (mkTransCo coInner cRight)
                       in (ty', mkCheckedTrans ty ty' co')
        _ -> (ty, mkNomReflCo ty)

homSplitIndex :: TyCon -> Int -> Int
homSplitIndex tc nArgs =
  let bndrs = take nArgs (tyConBinders tc)
      namedIndices = [i + 1 | (i, b) <- zip [0 ..] bndrs, isNamedTyConBinder b]
   in foldl (const id) 0 namedIndices

-- ---------------------------------------------------------------------------
-- Phase 2: KBO Representation, Ordering, and Unfailing Completion
-- ---------------------------------------------------------------------------

toKBTerm :: VarSet -> Type -> KBTerm
toKBTerm patVars ty0 =
  case coreFullView ty0 of
    CastTy inner kco | isReflCo kco -> toKBTerm patVars inner
    TyVarTy tv
      | tv `elemVarSet` patVars -> KBVar (uKey tv) (tyVarKind tv)
      | otherwise -> KBRigid (Just (uKey tv)) ty0
    TermVarTy v -> KBRigid (Just (uKey v)) ty0
    LitTy lit -> KBNode (KHLit lit) [] ty0
    TermAppTy f arg
      | isJust (splitFunTy_maybe (varType f)) ->
          KBNode (KHTermApp f) [toKBTerm patVars arg] ty0
    AppTy f a
      | isJust (splitFunTy_maybe (typeKind f)) ->
          KBNode KHApp [toKBTerm patVars f, toKBTerm patVars a] ty0
    TyConApp tc args ->
      let nDep = homSplitIndex tc (length args)
          roles = drop nDep (nominalRolesPrefix (length args) tc)
          (depArgs, homArgs) = splitAt nDep args
       in if all (== Nominal) roles && all (noPatVars patVars) depArgs
            then KBNode (KHCon tc depArgs) (map (toKBTerm patVars) homArgs) ty0
            else KBRigid (Just (uKey (tyConName tc))) ty0
    _ -> KBRigid Nothing ty0
  where
    noPatVars pvs t = isEmptyVarSet (tyCoVarsOfType t `intersectVarSet` pvs)

seedGroundEquation :: (Type, Type, CoercionN) -> [KBRule]
seedGroundEquation (lhs, rhs, co) =
  let tL = toKBTerm emptyVarSet lhs
      tR = toKBTerm emptyVarSet rhs
      base = KBRule tL tR (PrGiven co) False
   in base : decomposeRule base

decomposeRule :: KBRule -> [KBRule]
decomposeRule (KBRule (KBNode (KHCon tc1 p1) as1 _) (KBNode (KHCon tc2 p2) as2 _) pr isAx)
  | not isAx
  , tc1 == tc2
  , isGenerativeTyCon tc1 Nominal
  , length p1 == length p2
  , and (zipWith tcEqType p1 p2)
  , length as1 == length as2 =
      let roles = drop (length p1) (nominalRolesPrefix (length p1 + length as1) tc1)
          children =
            [ KBRule a1 a2 (PrSel (length p1 + i) pr) False
            | (i, r, a1, a2) <- zip4 [0 ..] roles as1 as2
            , r == Nominal
            , a1 /= a2
            , kbTermType a1 `tcEqType` kbTermType a2
            ]
       in children ++ concatMap decomposeRule children
  where
    zip4 (w : ws) (x : xs) (y : ys) (z : zs) = (w, x, y, z) : zip4 ws xs ys zs
    zip4 _ _ _ _ = []
decomposeRule _ = []

collectReachableAxiomRules :: [Type] -> [KBRule]
collectReachableAxiomRules seedTys =
  let initTcs = nubBy (==) (concatMap (nonDetEltsUniqSet . tyConsOfType) seedTys)
      allTcs = take 48 (reachableTyCons Set.empty initTcs)
   in concatMap extractTyConAxiomRules allTcs
  where
    reachableTyCons _ [] = []
    reachableTyCons seen (tc : rest)
      | uKey tc `Set.member` seen = reachableTyCons seen rest
      | otherwise =
          let seen' = Set.insert (uKey tc) seen
              more =
                concatMap
                  (nonDetEltsUniqSet . tyConsOfType)
                  ( map (varType . binderVar) (tyConBinders tc)
                      ++ [tyConResKind tc]
                      ++ [dataConOrigResTy dc | isAlgTyCon tc && not (isClassTyCon tc), dc <- take 8 (tyConDataCons tc)]
                      ++ concat [coAxBranchLHS br ++ [coAxBranchRHS br] | (_, _, br) <- tyConBranches tc]
                  )
                  ++ [dataConTyCon dc | Just dc <- [isPromotedDataCon_maybe tc]]
           in tc : reachableTyCons seen' (more ++ rest)

    tyConBranches :: TyCon -> [(CoAxiom Branched, BranchIndex, CoAxBranch)]
    tyConBranches tc =
      case famTyConFlav_maybe tc of
        Just (ClosedTypeFamilyTyCon ctf)
          | Just ax <- closedTyFamCoAxiom_maybe ctf ->
              [(ax, idx, br) | (idx, br) <- zip [0 :: Int ..] (fromBranches (coAxiomBranches ax))]
        _ -> []

    extractTyConAxiomRules tc =
      [ KBRule lhsTerm rhsTerm (PrAxiom ax idx tvs prefixPats rhsTy) True
      | (ax, idx, br) <- tyConBranches tc
      , null (coAxBranchCoVars br)
      , let tvs = coAxBranchTyVars br
      , all (\tv -> isTyVar tv) tvs
      , let patSet = mkVarSet tvs
      , let lhsArgs = coAxBranchLHS br
      , let nDep = homSplitIndex tc (length lhsArgs)
      , let (depArgs, homArgs) = splitAt nDep lhsArgs
      , let roles = drop nDep (nominalRolesPrefix (length lhsArgs) tc)
      , all (== Nominal) roles
      , let prefixPats = map (toKBTerm patSet) depArgs
      , let homPats = map (toKBTerm patSet) homArgs
      , let lhsTy = mkTyConApp tc lhsArgs
      , let rhsTy = coAxBranchRHS br
      , typeKind lhsTy `tcEqType` typeKind rhsTy
      , let lhsTerm = KBNode (KHCon tc depArgs) homPats lhsTy
      , let rhsTerm = toKBTerm patSet rhsTy
      , Set.fromList (kbPatternVars rhsTerm) `Set.isSubsetOf` Set.fromList (concatMap kbPatternVars (prefixPats ++ homPats))
      ]

kbPatternVars :: KBTerm -> [UKey]
kbPatternVars (KBVar u _) = [u]
kbPatternVars (KBRigid _ _) = []
kbPatternVars (KBNode _ as _) = concatMap kbPatternVars as

kboCompareGround :: KBTerm -> KBTerm -> Ordering
kboCompareGround s t =
  compare (kbWeight s) (kbWeight t) <> tie s t
  where
    tie (KBNode h1 as1 _) (KBNode h2 as2 _) =
      compareHead h1 h2 <> foldr (<>) EQ (zipWith kboCompareGround as1 as2)
    tie (KBNode {}) _ = GT
    tie _ (KBNode {}) = LT
    tie (KBRigid u1 t1) (KBRigid u2 t2) =
      case compare u1 u2 of
        EQ -> compare (showSDocUnsafe (ppr t1)) (showSDocUnsafe (ppr t2))
        other -> other
    tie (KBRigid {}) (KBVar {}) = GT
    tie (KBVar {}) (KBRigid {}) = LT
    tie (KBVar u1 _) (KBVar u2 _) = compare u1 u2

    compareHead KHApp KHApp = EQ
    compareHead KHApp _ = GT
    compareHead _ KHApp = LT
    compareHead (KHTermApp f1) (KHTermApp f2) =
      lexicalCompareFS (getOccFS f1) (getOccFS f2) <> compare (uKey f1) (uKey f2)
    compareHead (KHTermApp _) _ = GT
    compareHead _ (KHTermApp _) = LT
    compareHead (KHCon tc1 ps1) (KHCon tc2 ps2) =
      lexicalCompareFS (getOccFS tc1) (getOccFS tc2)
        <> compare (uKey tc1, length ps1) (uKey tc2, length ps2)
    compareHead (KHCon {}) _ = GT
    compareHead _ (KHCon {}) = LT
    compareHead (KHLit l1) (KHLit l2) =
      compare (showSDocUnsafe (ppr l1)) (showSDocUnsafe (ppr l2))

kboGreaterTemplate :: Map.Map UKey Int -> KBTerm -> KBTerm -> Bool
kboGreaterTemplate rank s t =
  let wCmp = compare (kbWeight s) (kbWeight t)
      diff = countVars (-1) t (countVars 1 s Map.empty)
      unrankedOk = and [cnt >= 0 | (u, cnt) <- Map.toList diff, u `Map.notMember` rank]
      rankedPairs = [(u, r) | (u, _) <- Map.toList diff, Just r <- [Map.lookup u rank]]
      rankedOk =
        and
          [ sum [Map.findWithDefault 0 u diff | (u, rj) <- rankedPairs, rj >= ri] >= 0
          | (_, ri) <- rankedPairs
          ]
   in wCmp /= LT && unrankedOk && rankedOk && (wCmp == GT || sameWeight s t)
  where
    countVars :: Int -> KBTerm -> Map.Map UKey Int -> Map.Map UKey Int
    countVars delta (KBVar u _) m = Map.insertWith (+) u delta m
    countVars _ (KBRigid _ _) m = m
    countVars delta (KBNode _ as _) m = foldr (countVars delta) m as

    sameWeight (KBNode h1 as1 _) (KBNode h2 as2 _)
      | h1 == h2 && length as1 == length as2 = lexArgs as1 as2
      | h1 /= h2 = compareHeadStrict h1 h2
    sameWeight (KBVar u1 _) (KBVar u2 _) =
      case (Map.lookup u1 rank, Map.lookup u2 rank) of
        (Just i, Just j) -> i > j
        _ -> False
    sameWeight _ _ = False

    lexArgs [] [] = False
    lexArgs (a : as) (b : bs)
      | a == b = lexArgs as bs
      | otherwise = kboGreaterTemplate rank a b
    lexArgs _ _ = False

    compareHeadStrict h1 h2 =
      kboCompareGround (KBNode h1 [] liftedTypeKind) (KBNode h2 [] liftedTypeKind) == GT

partitionRules :: [KBRule] -> ([KBRule], [KBRule])
partitionRules = foldr insertRule ([], [])
  where
    insertRule rule@(KBRule l r pr isAx) (ori, unori)
      | isAx = (rule : ori, unori)
      | kboGreaterTemplate Map.empty l r = (rule : ori, unori)
      | kboGreaterTemplate Map.empty r l = (KBRule r l (PrSym pr) False : ori, unori)
      | otherwise =
          let fwdVars = Set.fromList (kbPatternVars r) `Set.isSubsetOf` Set.fromList (kbPatternVars l)
              bwdVars = Set.fromList (kbPatternVars l) `Set.isSubsetOf` Set.fromList (kbPatternVars r)
              addFwd = [rule | fwdVars]
              addBwd = [KBRule r l (PrSym pr) False | bwdVars]
           in (ori, addFwd ++ addBwd ++ unori)

completeKB :: Int -> Int -> [KBRule] -> [KBRule] -> [KBRule] -> ([KBRule], [KBRule])
completeKB maxFuel maxNodes = loop 0
  where
    loop _ ori unori [] = (ori, unori)
    loop taken ori unori (cur : queue)
      | taken >= maxFuel = (ori, unori)
      | otherwise =
          let candidates = [r | r <- ori ++ unori, not (krIsAxiom cur && krIsAxiom r)]
              pairs = concatMap (criticalPairsBetween cur) candidates
              (ori', unori', added) = foldl processPair (ori, unori, []) pairs
           in loop (taken + 1) ori' unori' (queue ++ added)
      where
        processPair acc@(o, u, newQ) (s0, t0, pr0) =
          let (s1, prS) = rewriteGroundFix o u 16 s0
              (t1, prT) = rewriteGroundFix o u 16 t0
           in if s1 == t1
                || kbNodeCount s1 > maxNodes
                || kbNodeCount t1 > maxNodes
                || groundJoinable o u s1 t1
                then acc
                else
                  let combined = PrTrans (PrSym prS) (PrTrans pr0 prT)
                      baseRule = KBRule s1 t1 combined False
                      derived = baseRule : decomposeRule baseRule
                      (oNew, uNew) = partitionRules derived
                   in (oNew ++ o, uNew ++ u, newQ ++ derived)

criticalPairsBetween :: KBRule -> KBRule -> [(KBTerm, KBTerm, ProofRecipe)]
criticalPairsBetween r1 r2
  | not (null (kbPatternVars (krLhs r1))) || not (null (kbPatternVars (krLhs r2))) =
      -- Ground Given superposition against ground Givens or open SourceTable axioms:
      superpose r1 r2 ++ superpose r2 r1
  | otherwise =
      superpose r1 r2 ++ superpose r2 r1
  where
    superpose outer inner
      | not (null (kbPatternVars (krLhs outer))) = []
      | otherwise =
          [ (krRhs outer, putCtx rhsInnerInst, PrTrans (PrSym (krProof outer)) (mkCtxProof (PrSubst subst (krProof inner))))
          | (sub, putCtx, mkCtxProof) <- groundContexts (krLhs outer)
          , Just subst <- [matchKBTerm (krLhs inner) sub Map.empty]
          , Just rhsInnerInst <- [substKBTerm subst (krRhs inner)]
          ]

groundContexts :: KBTerm -> [(KBTerm, KBTerm -> KBTerm, ProofRecipe -> ProofRecipe)]
groundContexts t@(KBNode hd args ty) =
  (t, id, id)
    : [ ( sub
        , \rep ->
            let args' = take idx args ++ [rep] ++ drop (idx + 1) args
                ty' = rebuildNodeType hd args' ty
             in KBNode hd args' ty'
        , \subPr ->
            let prs =
                  [ if j == idx then subPr else PrRefl (kbTermType a)
                  | (j, a) <- zip [0 ..] args
                  ]
             in PrCong hd prs
        )
      | (idx, child) <- zip [0 ..] args
      , (sub, _, _) <- [(child, id, id)]
      ]
    ++ [ ( sub
         , \rep ->
             let child' = putChild rep
                 args' = take idx args ++ [child'] ++ drop (idx + 1) args
                 ty' = rebuildNodeType hd args' ty
              in KBNode hd args' ty'
         , \subPr ->
             let childPr = mkChildPr subPr
                 prs =
                   [ if j == idx then childPr else PrRefl (kbTermType a)
                   | (j, a) <- zip [0 ..] args
                   ]
              in PrCong hd prs
         )
       | (idx, child) <- zip [0 ..] args
       , (sub, putChild, mkChildPr) <- drop 1 (groundContexts child)
       ]
groundContexts _ = []

rebuildNodeType :: KBHead -> [KBTerm] -> Type -> Type
rebuildNodeType (KHCon tc pArgs) args _ = mkTyConApp tc (pArgs ++ map kbTermType args)
rebuildNodeType (KHTermApp f) [arg] _ = TermAppTy f (kbTermType arg)
rebuildNodeType KHApp [f, a] _ = mkAppTy (kbTermType f) (kbTermType a)
rebuildNodeType _ _ fallback = fallback

groundJoinable :: [KBRule] -> [KBRule] -> KBTerm -> KBTerm -> Bool
groundJoinable ori unori s t =
  let vs = nubBy (==) (kbPatternVars s ++ kbPatternVars t)
   in if null vs
        then fst (rewriteGroundFix ori unori 12 s) == fst (rewriteGroundFix ori unori 12 t)
        else
          length vs <= 3
            && all
              ( \perm ->
                  let rank = Map.fromList (zip perm [0 :: Int ..])
                   in rewriteRanked ori rank (8 :: Int) s == rewriteRanked ori rank (8 :: Int) t
              )
              (permutations vs)
  where
    rewriteRanked _ _ 0 cur = cur
    rewriteRanked rules rank fuel cur =
      case stepRanked rules rank cur of
        Nothing -> cur
        Just next -> rewriteRanked rules rank (fuel - 1) next

    stepRanked rules rank cur =
      let topMatch =
            [ rhs'
            | rule <- rules
            , Just subst <- [matchKBTerm (krLhs rule) cur Map.empty]
            , Just rhs' <- [substKBTerm subst (krRhs rule)]
            , kboGreaterTemplate rank cur rhs'
            ]
       in case topMatch of
            r' : _ -> Just r'
            [] ->
              case cur of
                KBNode hd args ty -> stepArgs hd [] args ty
                _ -> Nothing
      where
        stepArgs _ _ [] _ = Nothing
        stepArgs hd revPre (a : as) ty =
          case stepRanked rules rank a of
            Just a' ->
              let args' = reverse revPre ++ (a' : as)
               in Just (KBNode hd args' (rebuildNodeType hd args' ty))
            Nothing -> stepArgs hd (a : revPre) as ty

-- ---------------------------------------------------------------------------
-- Matching, Normalization, and Proof Materialization
-- ---------------------------------------------------------------------------

matchKBTerm :: KBTerm -> KBTerm -> Map.Map UKey KBTerm -> Maybe (Map.Map UKey KBTerm)
matchKBTerm (KBVar u k) target subst = do
  guard (k `tcEqType` typeKind (kbTermType target) || k `tcEqType` kbTermType target)
  case Map.lookup u subst of
    Nothing -> Just (Map.insert u target subst)
    Just prev -> guard (prev == target) >> Just subst
matchKBTerm (KBRigid u1 t1) (KBRigid u2 t2) subst = do
  guard (u1 == u2 && t1 `tcEqType` t2)
  Just subst
matchKBTerm (KBNode h1 as1 _) (KBNode h2 as2 _) subst
  | length as1 == length as2 = do
      subst1 <- matchKBHead h1 h2 subst
      foldM (\m (p, x) -> matchKBTerm p x m) subst1 (zip as1 as2)
matchKBTerm _ _ _ = Nothing

matchKBHead :: KBHead -> KBHead -> Map.Map UKey KBTerm -> Maybe (Map.Map UKey KBTerm)
matchKBHead (KHCon tc1 ps1) (KHCon tc2 ps2) subst
  | tc1 == tc2 && length ps1 == length ps2 =
      foldM matchPrefixType subst (zip ps1 ps2)
  where
    matchPrefixType m (pTy, tTy)
      | pTy `tcEqType` tTy = Just m
      | Just tv <- getTyVar_maybe pTy =
          let u = uKey tv
              target = KBRigid Nothing tTy
           in case Map.lookup u m of
                Nothing -> Just (Map.insert u target m)
                Just prev -> guard (kbTermType prev `tcEqType` tTy) >> Just m
      | Just (ptc, pargs) <- splitTyConApp_maybe pTy
      , Just (ttc, targs) <- splitTyConApp_maybe tTy
      , ptc == ttc
      , length pargs == length targs =
          foldM matchPrefixType m (zip pargs targs)
      | otherwise = Nothing
matchKBHead h1 h2 subst
  | h1 == h2 = Just subst
  | otherwise = Nothing

substKBTerm :: Map.Map UKey KBTerm -> KBTerm -> Maybe KBTerm
substKBTerm subst (KBVar u _) = Map.lookup u subst
substKBTerm _ r@(KBRigid _ _) = Just r
substKBTerm subst (KBNode hd args ty) = do
  hd' <- substKBHead subst hd
  args' <- traverse (substKBTerm subst) args
  let ty' = rebuildNodeType hd' args' (substGhcType subst ty)
  pure (KBNode hd' args' ty')

substKBHead :: Map.Map UKey KBTerm -> KBHead -> Maybe KBHead
substKBHead subst (KHCon tc pArgs) =
  Just (KHCon tc (map (substGhcType subst) pArgs))
substKBHead _ hd = Just hd

substGhcType :: Map.Map UKey KBTerm -> Type -> Type
substGhcType subst = go
  where
    go ty =
      case coreFullView ty of
        TyVarTy tv
          | Just term <- Map.lookup (uKey tv) subst -> kbTermType term
        TyConApp tc args -> mkTyConApp tc (map go args)
        AppTy f a -> mkAppTy (go f) (go a)
        FunTy af ma mult a r -> FunTy af (go ma) (go mult) (go a) (go r)
        other -> other

rewriteGroundFix :: [KBRule] -> [KBRule] -> Int -> KBTerm -> (KBTerm, ProofRecipe)
rewriteGroundFix ori unori maxSteps start = loop maxSteps start (PrRefl (kbTermType start))
  where
    loop 0 cur accPr = (cur, accPr)
    loop fuel cur accPr =
      case rewriteGroundStep ori unori cur of
        Nothing -> (cur, accPr)
        Just (next, stepPr) -> loop (fuel - 1) next (PrTrans accPr stepPr)

rewriteGroundStep :: [KBRule] -> [KBRule] -> KBTerm -> Maybe (KBTerm, ProofRecipe)
rewriteGroundStep ori unori = go
  where
    go term =
      tryTop ori term
        <|> tryTop unori term
        <|> case term of
          KBNode hd args ty -> stepChildren hd [] args ty
          _ -> Nothing

    tryTop [] _ = Nothing
    tryTop (rule : rest) term =
      case tryOne rule term of
        Just hit -> Just hit
        Nothing -> tryTop rest term

    tryOne rule term = do
      subst <- matchKBTerm (krLhs rule) term Map.empty
      rhs' <- substKBTerm subst (krRhs rule)
      guard (kbTermType term `tcEqType` kbTermType rhs' || typeKind (kbTermType term) `tcEqType` typeKind (kbTermType rhs'))
      guard (krIsAxiom rule || kboCompareGround term rhs' == GT)
      let pr = PrSubst subst (krProof rule)
      -- Verify the proof materializes cleanly (checking apartnessCheck on axioms!)
      _ <- evalProof Map.empty pr
      pure (rhs', pr)

    stepChildren _ _ [] _ = Nothing
    stepChildren hd revPre (a : as) ty =
      case go a of
        Just (a', prA) ->
          let args' = reverse revPre ++ (a' : as)
              prs = map (PrRefl . kbTermType) (reverse revPre) ++ [prA] ++ map (PrRefl . kbTermType) as
              ty' = rebuildNodeType hd args' ty
           in Just (KBNode hd args' ty', PrCong hd prs)
        Nothing -> stepChildren hd (a : revPre) as ty

normalizeGroundKB :: KBEnv -> Int -> Type -> (Type, CoercionN)
normalizeGroundKB env maxSteps ty0 =
  let start = toKBTerm emptyVarSet ty0
      (end, recipe) = rewriteGroundFix (kbeOriented env) (kbeUnoriented env) maxSteps start
      endTy = kbTermType end
   in case evalProof Map.empty recipe of
        Just co
          | let Pair l r = coercionKind co
          , l `tcEqType` ty0 && r `tcEqType` endTy ->
              (endTy, co)
        _ -> (ty0, mkNomReflCo ty0)

evalProof :: Map.Map UKey Type -> ProofRecipe -> Maybe CoercionN
evalProof env = \case
  PrRefl ty -> Just (mkNomReflCo (applyEnv env ty))
  PrGiven co -> Just co
  PrAxiom ax idx tvs _ _ -> do
    instTys <- traverse (\tv -> Map.lookup (uKey tv) env) tvs
    let br = coAxiomNthBranch ax idx
        subst = zipTvSubst tvs instTys
        lhsInst = substTys subst (coAxBranchLHS br)
    guard (apartnessCheck lhsInst br)
    pure (mkAxInstCo Nominal (BranchedAxiom ax idx) instTys [])
  PrSel i inner -> do
    co <- evalProof env inner
    let Pair l r = coercionKind co
    case (splitTyConApp_maybe l, splitTyConApp_maybe r) of
      (Just (tc1, as1), Just (tc2, as2))
        | tc1 == tc2
        , isGenerativeTyCon tc1 Nominal
        , i < length as1
        , i < length as2
        , nominalRolesPrefix (i + 1) tc1 !! i == Nominal ->
            Just (mkSelCo (SelTyCon i Nominal) co)
      _ -> Nothing
  PrSym inner -> mkSymCo <$> evalProof env inner
  PrTrans p q -> do
    co1 <- evalProof env p
    co2 <- evalProof env q
    let Pair _ r1 = coercionKind co1
        Pair l2 _ = coercionKind co2
    guard (r1 `tcEqType` l2)
    pure (mkTransCo co1 co2)
  PrCong hd childRecipes -> do
    childCos <- traverse (evalProof env) childRecipes
    case (hd, childCos) of
      (KHCon tc pArgs, _) ->
        let pArgs' = map (applyEnv env) pArgs
         in Just (mkTyConAppCo Nominal tc (map mkNomReflCo pArgs' ++ childCos))
      (KHTermApp f, [cArg]) -> Just (mkTermAppCo f cArg)
      (KHApp, [cF, cA]) -> Just (mkAppCo cF cA)
      (KHLit lit, []) -> Just (mkNomReflCo (LitTy lit))
      _ -> Nothing
  PrSubst subst inner ->
    let env' = Map.map (applyEnv env . kbTermType) subst `Map.union` env
     in evalProof env' inner
  where
    applyEnv m ty
      | Map.null m = ty
      | otherwise = go ty
      where
        go t =
          case coreFullView t of
            TyVarTy tv -> fromMaybe t (Map.lookup (uKey tv) m)
            TyConApp tc args -> mkTyConApp tc (map go args)
            AppTy f a -> mkAppTy (go f) (go a)
            FunTy af ma mult a r -> FunTy af (go ma) (go mult) (go a) (go r)
            other -> other
