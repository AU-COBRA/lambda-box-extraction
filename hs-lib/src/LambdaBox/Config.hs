-- Lambda Box configuration type definitions
-- Most fields are marked as optional, if set to Nothing
-- then the default value will be used
module LambdaBox.Config where

import qualified LambdaBox.LambdaBox



-- Rust backend configuration
data RustConfig = RustConfig
  { rustPreambleTop       :: Maybe String,
    rustPreambleProgram   :: Maybe String,
    rustTermBoxSymbol     :: Maybe String,
    rustTypeBoxSymbol     :: Maybe String,
    rustAnyTypeSyymbol    :: Maybe String,
    rustPrintFullNames    :: Maybe Bool,
    rustDefaultAttributes :: Maybe String
  }

-- Elm backend configuration
data ElmConfig = ElmConfig
  { elmPreamble       :: Maybe String,
    elmModuleName     :: Maybe String,
    elmTermBoxSymbol  :: Maybe String,
    elmTypeBoxSymbol  :: Maybe String,
    elmAnyTypeSyymbol :: Maybe String,
    elmFalseElimDef   :: Maybe String,
    elmPrintFullNames :: Maybe Bool
  }

-- CertiRocq (C & Webassembly) backend configuration
data CertiRocqConfig = CertiRocqConfig
  { direct    :: Maybe Bool,
    cArgs     :: Maybe Int,
    oLevel    :: Maybe Int,
    anfConf   :: Maybe Int,
    prefix    :: Maybe String,
    bodyName  :: Maybe String
  }

-- OCaml backend configuration
data ProgramType
  = Standalone
  --Reference to a plugin registration function
  | SharedLib String String

data OCamlConfig = OCamlConfig
  { programType :: Maybe ProgramType
  }

-- Lean backend configuration
data LeanConfig = LeanConfig
  { leanNamespace      :: Maybe String,
    leanPrintFullNames :: Maybe Bool
  }

-- CakeML backend configuration
type CakeMLConfig = ()

-- Eval backend configuration
data EvalConfig = EvalConfig
  { copts    :: Maybe CertiRocqConfig,
    fuel     :: Int,
    evalAnf :: Bool
  }

-- AST backend configuration
data ASTType
  = LambdaBox
  | LambdaBoxTyped
  | LambdaBoxMut (Maybe CertiRocqConfig)
  | LambdaBoxLocal (Maybe CertiRocqConfig)
  | LambdaANF (Maybe CertiRocqConfig)
  | LambdaANFC (Maybe CertiRocqConfig)

data ASTConfig = ASTConfig
  { astType :: ASTType
  }

-- Backend configuration
-- States the backend that Peregrine should use along
-- with with options specific to that backend
data BackendConfig
  = Rust RustConfig
  | Elm ElmConfig
  | C CertiRocqConfig
  | Wasm CertiRocqConfig
  | OCaml OCamlConfig
  | CakeML CakeMLConfig
  | Lean LeanConfig
  | Eval EvalConfig
  | AST ASTConfig



-- Inductive remapping
data RemappedInductive = RemappedInductive
  { indName   :: String,
    indCtors  :: [String],
    indMatch  :: Maybe String
  }

data ExtractInductive = ExtractInductive
  { cstrs :: [LambdaBox.LambdaBox.KerName],
    elim  :: LambdaBox.LambdaBox.KerName
  }

data RemapInductive
  = KnIndRemap LambdaBox.LambdaBox.KerName [ExtractInductive]
  | StringIndRemap LambdaBox.LambdaBox.Inductive RemappedInductive

type InductiveRemappings = [RemapInductive]

-- Constant remapping
data RemappedConstant = RemappedConstant
  { reConstExt   :: Maybe String,
    reConstArity :: Int,
    reConstGC    :: Bool,
    reConstInl   :: Bool,
    reConstS     :: String
  }

type ConstantRemappings = [(LambdaBox.LambdaBox.KerName, RemappedConstant)]

-- Constructor reorder annotations
type InductiveMapping = (LambdaBox.LambdaBox.Inductive, (String, [Int]))
type InductivesMapping = [InductiveMapping]

-- Inlining annotations
type Inlinings = [LambdaBox.LambdaBox.KerName]

-- Custom attributes
type CustomAttributes = [(LambdaBox.LambdaBox.KerName, String)]

-- Configure optional compilation phases
data ErasurePhases = ErasurePhases
  { implementBox  :: Maybe Bool,
    implementLaxy :: Maybe Bool,
    cofixToLazy   :: Maybe Bool,
    betared       :: Maybe Bool,
    unboxing      :: Maybe Bool,
    deargCtor     :: Maybe Bool,
    deargConst    :: Maybe Bool
  }

-- Configuration of Peregrine
data Config = Config
  { backendOpts       :: BackendConfig,
    erasureOpts       :: Maybe ErasurePhases,
    inlinings         :: Inlinings,
    constRemappings   :: ConstantRemappings,
    indRemappings     :: InductiveRemappings,
    cstrReorders      :: InductivesMapping,
    customAttributes  :: CustomAttributes
  }

-- Attributes configuration
data AttributesConfig = AttributesConfig
  { inlinings'         :: Inlinings,
    constRemappings'   :: ConstantRemappings,
    indRemappings'     :: InductiveRemappings,
    cstrReorders'      :: InductivesMapping,
    customAttributes'  :: CustomAttributes
  }
