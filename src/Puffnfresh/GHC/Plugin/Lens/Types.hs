module Puffnfresh.GHC.Plugin.Lens.Types where

import qualified GhcPlugins as P
import qualified GHC.Hs as Hs
import Control.Lens (Lens', (^.), (^..), to)

data Constructors
  = ZeroConstructors
  | OneConstructor ConstructorDeclaration
  | ManyConstructors ConstructorDeclaration ConstructorDeclaration [ConstructorDeclaration]

instance P.Outputable Constructors where
  ppr ZeroConstructors =
    P.text "<Void>"
  ppr (OneConstructor a) =
    P.ppr a
  ppr (ManyConstructors a b as) =
    P.pprWithBars P.ppr (a:b:as)

data Parameters
  = ZeroParameters
  | OneParameter (Hs.HsType Hs.GhcPs)
  | ManyParameters (Hs.HsType Hs.GhcPs) (Hs.HsType Hs.GhcPs) [Hs.HsType Hs.GhcPs]

instance P.Outputable Parameters where
  ppr ZeroParameters =
    P.text "()"
  ppr (OneParameter a) =
    P.ppr a
  ppr (ManyParameters a b as) =
    P.interppSP (a:b:as)

data ConstructorDeclaration
  = ConstructorDeclaration P.RdrName Parameters

instance P.Outputable ConstructorDeclaration where
  ppr (ConstructorDeclaration a b) =
    P.ppr a P.<+> P.ppr b

data DataDeclaration
  = DataDeclaration P.RdrName (Hs.LHsQTyVars Hs.GhcPs) Constructors

instance P.Outputable DataDeclaration where
  ppr (DataDeclaration a b c) = P.text "data" P.<+> P.ppr a P.<+> P.ppr b P.<+> P.text "=" P.<+> P.ppr c

located
  :: Lens' (P.GenLocated a b) b
located f (P.L a b) =
  (P.L a) <$> f b

hpm_module'
  :: Lens' P.HsParsedModule (P.Located (Hs.HsModule Hs.GhcPs))
hpm_module' f (P.HsParsedModule a b c) =
  (\a' -> P.HsParsedModule a' b c) <$> f a

hsmodDecls'
  :: Lens' (Hs.HsModule a) [Hs.LHsDecl a]
hsmodDecls' g (Hs.HsModule a b c d e f) =
  (\d' -> Hs.HsModule a b c d' e f) <$> g d

constructors :: [ConstructorDeclaration] -> Constructors
constructors [] =
  ZeroConstructors
constructors [a] =
  OneConstructor a
constructors (a:b:as) =
  ManyConstructors a b as

parameters :: [Hs.HsType Hs.GhcPs] -> Parameters
parameters [] =
  ZeroParameters
parameters [a] =
  OneParameter a
parameters (a:b:as) =
  ManyParameters a b as

conDecl' :: Hs.ConDecl Hs.GhcPs -> Maybe ConstructorDeclaration
conDecl' (Hs.ConDeclH98 _ a _ _ _ (Hs.PrefixCon b) _) =
  Just (ConstructorDeclaration (a ^. located) (parameters (b ^.. traverse . located)))
conDecl' _ =
  Nothing

hsDecl' :: Hs.HsDecl Hs.GhcPs -> Maybe DataDeclaration
hsDecl' (Hs.TyClD _ (Hs.DataDecl _ (P.L _ a) b _ (Hs.HsDataDefn _ _ _ _ _ c _))) =
  Just (DataDeclaration a b (constructors (c ^.. traverse . located . to conDecl' . traverse)))
hsDecl' _ =
  Nothing
