# Puffnfresh's GHC Plugin for Lens

Takes the following:

```
{-# OPTIONS_GHC -fplugin=Puffnfresh.GHC.Plugin.Lens #-}

data X = X

data Y = Y1 | Y2 Int

data Z a = Z1 a Int | Z2 Char
```

And generates:

```
_X :: Iso' X ()

_Y1 :: Prism' Y ()
_Y2 :: Prism' Y Int

_Z1 :: Prism' (Z a) (a, Int)
_Z2 :: Prism' (Z a) Char
```
