# Peregrine Pipeline

![](/doc/peregrine.png)

Peregrine framework is made up of 5 components frontends, the middle-end, backends, the $\lambda_\square$ IR and configuration format.

# $\lambda_\square$ and configuration

$\lambda_\square$ (untyped) and $\lambda_{\square}^T$ (typed) is the intermediate representations used in Peregrine.
It is produced by the frontends. The middle-end further processes $\lambda_\square$, which is then passed to the backends to compile it to the target language.

S-expressions are used for serialization to communicate between the frontends, middle-end, and backends.
In addition to passing serialized ASTs the components also exchange serialized configuration.

For more details see [format.md](/doc/format.md)

# Frontends

Peregrine frontends produce $\lambda_\square$ from a source langauge / proof assistant through proof-erasure.

For more details see [frontends.md](/doc/frontends.md)

# Middle-end

The middle-end connects frontends and backends and serves three purposes:

1) Defines a common IR and configuration format and is responsible for converting to the formats expected by the backends.
2) Validates and ensure $\lambda_\square$ and frontend/backend configuration is compatible
3) Lower $\lambda_\square$ to the necessary subset compatible with the backends, and apply common program transformations and optimizations

For more details see [middleend.md](/doc/middleend.md)

# Backends

Backends translate $\lambda_\square$ into another programming langauge, e.g. C, OCaml, or Rust.

For more details see [backends.md](/doc/backends.md)
