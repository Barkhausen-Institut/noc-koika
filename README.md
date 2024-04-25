# noc-koika

This project implements a Network-on-Chip (NoC) in [Koika](https://github.com/mit-plv/koika).
Koika is a DSL for hardware design embedded in Coq.

## Setup

Please use [`nix`](https://nixos.org/download.html) to get all the setup you need for this project.
Please [enable `flake` support in `nix`](https://nixos.wiki/wiki/Flakes).
If the `~/.config/nix/` folder and/or the `~/.config/nix/nix.conf` file do not exist then just create them.

After that all you need to issue at the command line is:
```
nix develop
```
Be prepared to wait a while because it will essentially build everything from scratch, even Coq itself.

Currently there is no package for Spacemacs on Nix. Hence, we suggest to install it from inside the `nix shell`.

- First, you need to install `emacs`.
- [Here](https://www.spacemacs.org/#) you can find the command to install Spacemacs.
- But instead install `spacemacs` right at the root project directory via
  ```git clone https://github.com/syl20bnr/spacemacs .emacs.d```
- Start emacs now like so: `spacemacs`.
- Once installation is complete you need to [edit the config](https://develop.spacemacs.org/doc/QUICK_START.html) and [activate the Coq layer](https://develop.spacemacs.org/layers/+lang/coq/README.html).
- [optional] For prettification and other fancy stuff, please install [`company-coq`](https://github.com/cpitclaudel/company-coq) with `<SPC> <SPC> package-install <RET> company-coq <RET>`

## Build

To build the project, please run
```
dune build
```
