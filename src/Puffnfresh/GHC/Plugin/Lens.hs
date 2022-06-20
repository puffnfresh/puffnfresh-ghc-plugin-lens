module Puffnfresh.GHC.Plugin.Lens where

import Data.Foldable (for_)
import qualified GhcPlugins as P
import qualified GHC.Hs as Hs
import qualified BasicTypes as BT
import qualified TcEvidence as Tc
import Data.String (fromString)
import Control.Lens (Traversal', Lens', Fold, (^.), (^..), (&), (%~), to)
import Puffnfresh.GHC.Plugin.Lens.Types

plugin
  :: P.Plugin
plugin =
  P.defaultPlugin
    { P.parsedResultAction = \_ _ -> addLenses
    , P.pluginRecompile = P.purePlugin
    }

sig :: P.RdrName -> Hs.LHsQTyVars Hs.GhcPs -> P.RdrName -> Parameters -> P.RdrName -> Hs.HsDecl Hs.GhcPs
sig tyName (Hs.HsQTvs _ tvs) name ps tc =
  Hs.SigD Hs.noExtField (Hs.TypeSig Hs.noExtField [P.noLoc name'] (Hs.HsWC Hs.noExtField (Hs.HsIB Hs.noExtField (P.noLoc (Hs.HsAppTy Hs.noExtField (P.noLoc (Hs.HsAppTy Hs.noExtField (P.noLoc (Hs.HsTyVar Hs.noExtField BT.NotPromoted (P.noLoc tc))) (P.noLoc isoFromType))) (P.noLoc isoToType))))))
  where
    isoFromType =
      (if null tvs
        then id
        else Hs.HsParTy Hs.noExtField . P.noLoc)
      (foldl (\y x -> Hs.HsAppTy Hs.noExtField (P.noLoc y) (P.noLoc (Hs.HsTyVar Hs.noExtField BT.NotPromoted (P.noLoc x)))) (Hs.HsTyVar Hs.noExtField BT.NotPromoted (P.noLoc tyName)) tvs')
    isoToType =
      case ps of
        ZeroParameters ->
          Hs.HsTupleTy Hs.noExtField Hs.HsBoxedTuple []
        OneParameter p ->
          p
        ManyParameters p1 p2 ps ->
          Hs.HsTupleTy Hs.noExtField Hs.HsBoxedTuple (P.noLoc <$> (p1:p2:ps))
    tvs' =
      tvs >>= \t -> case t of
        P.L _ (Hs.UserTyVar _ (P.L _ x)) ->
          [x]
        _ ->
          []
    name' =
      P.mkVarUnqual (fromString "_" <> P.occNameFS (P.rdrNameOcc name))

val' :: P.RdrName -> Hs.HsExpr Hs.GhcPs -> Hs.HsDecl Hs.GhcPs
val' name body =
  Hs.ValD Hs.noExtField (Hs.FunBind Hs.noExtField (P.noLoc name') (Hs.MG Hs.noExtField (P.noLoc [P.noLoc match]) BT.Generated) Tc.WpHole [])
  where
    match =
      Hs.Match Hs.noExtField (Hs.FunRhs (P.noLoc name') BT.Prefix Hs.NoSrcStrict) [] (Hs.GRHSs Hs.noExtField [P.noLoc (Hs.GRHS Hs.noExtField [] (P.noLoc body))] (P.noLoc (Hs.EmptyLocalBinds Hs.noExtField)))
    name' =
      P.mkVarUnqual (fromString "_" <> P.occNameFS (P.rdrNameOcc name))

val :: P.RdrName -> Parameters -> ((Hs.HsMatchContext P.RdrName -> Hs.HsExpr Hs.GhcPs -> Hs.Match Hs.GhcPs (Hs.LHsExpr Hs.GhcPs)) -> Hs.HsExpr Hs.GhcPs -> Hs.HsExpr Hs.GhcPs -> Hs.HsExpr Hs.GhcPs) -> Hs.HsDecl Hs.GhcPs
val c ps body =
  val' c (body matchConstructor makeTuple tupleToConstructor)
  where
    paramCount =
      case ps of
        ZeroParameters ->
          0
        OneParameter _ ->
          1
        ManyParameters _ _ ps ->
          length ps + 2
    matchConstructor context body' =
      Hs.Match Hs.noExtField context [P.noLoc patConstructor] (Hs.GRHSs Hs.noExtField [P.noLoc (Hs.GRHS Hs.noExtField [] (P.noLoc body'))] (P.noLoc (Hs.EmptyLocalBinds Hs.noExtField)))
    makeTuple =
      case ps of
        ZeroParameters ->
          Hs.ExplicitTuple Hs.noExtField [] BT.Boxed
        OneParameter p ->
          Hs.HsVar Hs.noExtField (P.noLoc (P.mkVarUnqual (fromString "a")))
        ManyParameters _ _ _ ->
          Hs.ExplicitTuple Hs.noExtField (P.noLoc . Hs.Present Hs.noExtField . P.noLoc . Hs.HsVar Hs.noExtField . P.noLoc <$> take paramCount names) BT.Boxed
    patVars =
      P.noLoc . Hs.VarPat Hs.noExtField . P.noLoc <$> take paramCount names
    patConstructor =
      case ps of
        ZeroParameters ->
          Hs.WildPat Hs.noExtField
        _ ->
          Hs.ParPat Hs.noExtField (P.noLoc (Hs.ConPatIn (P.noLoc c) (Hs.PrefixCon patVars)))
    matchTuple =
      Hs.Match Hs.noExtField Hs.LambdaExpr [P.noLoc patTuple] (Hs.GRHSs Hs.noExtField [P.noLoc (Hs.GRHS Hs.noExtField [] (P.noLoc (foldl (\s p -> Hs.HsApp Hs.noExtField (P.noLoc s) (P.noLoc (Hs.HsVar Hs.noExtField (P.noLoc p)))) (Hs.HsVar Hs.noExtField (P.noLoc c)) (take paramCount names))))] (P.noLoc (Hs.EmptyLocalBinds Hs.noExtField)))
    patTuple =
      case ps of
        ZeroParameters ->
          Hs.WildPat Hs.noExtField
        OneParameter _ ->
          Hs.VarPat Hs.noExtField (P.noLoc (P.mkVarUnqual (fromString "a")))
        ManyParameters _ _ _ ->
          Hs.TuplePat Hs.noExtField patVars BT.Boxed

    tupleToConstructor =
      Hs.HsPar Hs.noExtField (P.noLoc (fmap_ (Hs.HsPar Hs.noExtField (P.noLoc (Hs.HsLam Hs.noExtField (Hs.MG Hs.noExtField (P.noLoc [P.noLoc matchTuple]) BT.Generated))))))

names :: [P.RdrName]
names = P.mkVarUnqual . fromString . (:[]) <$> ['a'..'z']

compose_ :: Hs.HsExpr Hs.GhcPs -> Hs.HsExpr Hs.GhcPs -> Hs.HsExpr Hs.GhcPs
compose_ ab cd =
  Hs.HsApp Hs.noExtField (P.noLoc (Hs.HsApp Hs.noExtField (P.noLoc (Hs.HsVar Hs.noExtField (P.noLoc name))) (P.noLoc ab))) (P.noLoc cd)
  where
    name =
      P.mkRdrQual (P.mkModuleName "Prelude") (P.mkVarOcc ".")

dimap_ :: Hs.HsExpr Hs.GhcPs -> Hs.HsExpr Hs.GhcPs -> Hs.HsExpr Hs.GhcPs
dimap_ ab cd =
  Hs.HsApp Hs.noExtField (P.noLoc (Hs.HsApp Hs.noExtField (P.noLoc (Hs.HsVar Hs.noExtField (P.noLoc name))) (P.noLoc ab))) (P.noLoc cd)
  where
    name =
      P.mkRdrQual (P.mkModuleName "Data.Profunctor") (P.mkVarOcc "dimap")

fmap_ :: Hs.HsExpr Hs.GhcPs -> Hs.HsExpr Hs.GhcPs
fmap_ ab =
  Hs.HsApp Hs.noExtField (P.noLoc (Hs.HsVar Hs.noExtField (P.noLoc name))) (P.noLoc ab)
  where
    name =
      P.mkRdrQual (P.mkModuleName "Prelude") (P.mkVarOcc "fmap")

either_ :: Hs.HsExpr Hs.GhcPs -> Hs.HsExpr Hs.GhcPs -> Hs.HsExpr Hs.GhcPs
either_ ab cd =
  Hs.HsApp Hs.noExtField (P.noLoc (Hs.HsApp Hs.noExtField (P.noLoc (Hs.HsVar Hs.noExtField (P.noLoc name))) (P.noLoc ab))) (P.noLoc cd)
  where
    name =
      P.mkRdrQual (P.mkModuleName "Data.Either") (P.mkVarOcc "either")

pure_ :: Hs.HsExpr Hs.GhcPs
pure_ =
  Hs.HsVar Hs.noExtField (P.noLoc name)
  where
    name =
      P.mkRdrQual (P.mkModuleName "Prelude") (P.mkVarOcc "pure")

_Left :: Hs.HsExpr Hs.GhcPs -> Hs.HsExpr Hs.GhcPs
_Left ab =
  Hs.HsApp Hs.noExtField (P.noLoc (Hs.HsVar Hs.noExtField (P.noLoc name))) (P.noLoc ab)
  where
    name =
      P.mkRdrQual (P.mkModuleName "Prelude") (P.mkDataOcc "Left")

_Right :: Hs.HsExpr Hs.GhcPs -> Hs.HsExpr Hs.GhcPs
_Right ab =
  Hs.HsApp Hs.noExtField (P.noLoc (Hs.HsVar Hs.noExtField (P.noLoc name))) (P.noLoc ab)
  where
    name =
      P.mkRdrQual (P.mkModuleName "Prelude") (P.mkDataOcc "Right")

right'_ :: Hs.HsExpr Hs.GhcPs
right'_ =
  Hs.HsVar Hs.noExtField (P.noLoc name)
  where
    name =
      P.mkRdrQual (P.mkModuleName "Data.Profunctor") (P.mkVarOcc "right'")

generateIso :: P.RdrName -> Hs.LHsQTyVars Hs.GhcPs -> ConstructorDeclaration -> [Hs.HsDecl Hs.GhcPs]
generateIso a tvs (ConstructorDeclaration c ps) =
  [ sig a tvs c ps _Iso'
  , val c ps body
  ]
  where
    _Iso' =
      P.mkRdrQual (P.mkModuleName "Control.Lens") (P.mkTcOcc "Iso'")

    body matchConstructor makeTuple tupleToConstructor =
      dimap_ (constructorToTuple (matchConstructor Hs.LambdaExpr makeTuple)) tupleToConstructor

    constructorToTuple :: Hs.Match Hs.GhcPs (Hs.LHsExpr Hs.GhcPs) -> Hs.HsExpr Hs.GhcPs
    constructorToTuple match =
      Hs.HsPar Hs.noExtField (P.noLoc (Hs.HsLam Hs.noExtField (Hs.MG Hs.noExtField (P.noLoc [P.noLoc match]) BT.Generated)))

generatePrism :: P.RdrName -> Hs.LHsQTyVars Hs.GhcPs -> ConstructorDeclaration -> [Hs.HsDecl Hs.GhcPs]
generatePrism a tvs (ConstructorDeclaration c ps) =
  [ sig a tvs c ps _Prism'
  , val c ps body
  ]
  where
    _Prism' =
      P.mkRdrQual (P.mkModuleName "Control.Lens") (P.mkTcOcc "Prism'")

    body matchConstructor makeTuple tupleToConstructor =
      compose_ (Hs.HsPar Hs.noExtField (P.noLoc (dimap_ (constructorToTuple (matchConstructor Hs.CaseAlt (_Right makeTuple))) (either_ pure_ tupleToConstructor)))) right'_

    constructorToTuple :: Hs.Match Hs.GhcPs (Hs.LHsExpr Hs.GhcPs) -> Hs.HsExpr Hs.GhcPs
    constructorToTuple match =
      Hs.HsPar Hs.noExtField (P.noLoc (Hs.HsLam Hs.noExtField (Hs.MG Hs.noExtField (P.noLoc [P.noLoc (Hs.Match Hs.noExtField Hs.LambdaExpr [P.noLoc (Hs.VarPat Hs.noExtField (P.noLoc (P.mkVarUnqual (fromString "z"))))] (Hs.GRHSs Hs.noExtField [P.noLoc (Hs.GRHS Hs.noExtField [] (P.noLoc (Hs.HsCase Hs.noExtField (P.noLoc (Hs.HsVar Hs.noExtField (P.noLoc (P.mkVarUnqual (fromString "z"))))) (Hs.MG Hs.noExtField (P.noLoc [
        P.noLoc match
      , P.noLoc (Hs.Match Hs.noExtField Hs.CaseAlt [P.noLoc (Hs.WildPat Hs.noExtField)] (Hs.GRHSs Hs.noExtField [P.noLoc (Hs.GRHS Hs.noExtField [] (P.noLoc (_Left (Hs.HsVar Hs.noExtField (P.noLoc (P.mkVarUnqual (fromString "z")))))))] (P.noLoc (Hs.EmptyLocalBinds Hs.noExtField))))
      ]) BT.Generated))))] (P.noLoc (Hs.EmptyLocalBinds Hs.noExtField))))]) BT.Generated)))

generate :: DataDeclaration -> [Hs.HsDecl Hs.GhcPs]
generate (DataDeclaration _ _ ZeroConstructors) =
  -- generateIso a b (error "void")
  []
generate (DataDeclaration a b (OneConstructor c)) =
  generateIso a b c
generate (DataDeclaration a b (ManyConstructors c d cs)) =
  (c:d:cs) >>= generatePrism a b

addLenses
  :: P.HsParsedModule
  -> P.Hsc P.HsParsedModule
addLenses modu =
  pure (modu & hpm_module' . traverse . hsmodDecls' %~ generateDecls)
  where
    generateDecls :: [Hs.LHsDecl Hs.GhcPs] -> [Hs.LHsDecl Hs.GhcPs]
    generateDecls decls =
      decls <> ((decls ^.. traverse . located . to hsDecl' . traverse) >>= fmap P.noLoc . generate)
