# Peregrine middle-end sources
This directory contains the Peregrine middle-end Rocq source code.

* [backends/](backends/): Wrappers for Peregrine backends
* [erasure/](erasure/): Code transform/optimization pipeline, and Rocq frontend utilities
* [serialization/](serialization/): Serializers, deserializers and correctness proofs
* [CheckWF.v](CheckWf.v): AST wellformedness checker
* [Config.v](Config.v): Configuration definitions
* [ConfigUtils.v](ConfigUtils.v): Configuration utilities
* [CoqToLambdaBox.v](CoqToLambdaBox.v): Rocq frontend
* [EvalBox.v](EvalBox.v): LambdaBox interpreter
* [Extraction.v](Extraction.v): Extracts middle-end to OCaml for use in CLI, extracted code in [src/extraction](/src/extraction/)
* [NameSanitize.v](NameSanitize.v): Name sanitization pass
* [PAst.v](PAst.v): AST definition
* [Pipeline.v](Pipeline.v): Main file defining the middle-end pipeline
* [Unicode.v](Unicode.v): Unicode definition and utilities
* [UnicodeXID.v](UnicodeXID.v): Unicode XID properties
* [Utils.v](Utils.v): Utilities
