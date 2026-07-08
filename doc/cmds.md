# Peregrine Command Line Interface
`peregrine --help` for detailed instructions


## `compile` command
```
peregrine compile [OPTION]… PROGRAM_FILE CONFIG_FILE
```

Compile lambda box program using the configuration declared in `CONFIG_FILE` the configuration includes the target backend.

## Backend commands
Commands for the specific backends, configuration file is optional for all of them, if a configuration exists then it is preferred to use the `compile` command instead.

```
peregrine BACKEND FILE [-o FILE]
```

Valid values for `BACKEND` are:
* `wasm`
* `c`
* `ocaml`
* `cakeml`
* `rust`
* `elm`
* `ast`
* `eval`

## `validate` command
```
peregrine validate [--config=PATH] [OPTION]… FILE
```

Runs program and optional configuration file validation.



## Common options
These options are common to all commands.

* `--attributes=PATH[,…]`
  Attribute config files, a list of files containing attribute configuration

* `-o VAL, --outfile=VAL`
  Output file

* `-d, --debug`
  Enable debug information

* `-q, --quiet`
  Suppress informational output

* `-v, --verbose`
  Give verbose output
