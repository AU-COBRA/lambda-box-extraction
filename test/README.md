# Peregrine tests

To run the tests suite run `npm run test`.

The test suite depends on the following:
* Node.js v22 or later
* cargo and rust compiler
* [elm compiler](https://elm-lang.org/)
* elm-test (can be installed with npm)
* gcc
* [.NET SDK](https://dotnet.microsoft.com/) 10 or later (`dotnet`)


## Agda frontend tests
These tests are Agda programs compiled to $\lambda_\square$ with the [agda2lambox](https://github.com/agda/agda2lambox/tree/master) tool.
The tests are from the [agda2lambox test suite](https://github.com/agda/agda2lambox/tree/master/test).

The untyped programs (`*.ast`) were compiled with default configuration.

The type programs (`*.tast`) were compiled with `--typed --no-block` flags.

To reproduce the files run:
```bash
#!/bin/bash
git clone git@github.com:agda/agda2lambox.git
cd agda2lambox
cabal install

for f in test/*.agda; do
  agda2lambox $f -o dist/
  agda2lambox --typed --no-block $f -o dist-typed/
done

for f in dist-typed/*.ast; do
    mv "$f" "${f%.ast}.tast"
done

find dist/. -type f -name "*.txt" -delete
find dist-typed/. -type f -name "*.txt" -delete
```

## Directory
* [src/](src/): Test runner source code
* [rocq/](rocq/): Rocq test programs
* [lean/](lean/): Lean test programs
