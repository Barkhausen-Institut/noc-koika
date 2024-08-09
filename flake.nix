{
  inputs = {
    nixpkgs.follows = "koika/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
    koika = {
      url = "github:Barkhausen-Institut/koika/master";
      inputs.flake-utils.follows = "flake-utils";
    };
  };

  outputs = { self, nixpkgs, flake-utils, koika }: let
    NocPkg = { lib, mkCoqDerivation, coq, equations, koika, metacoq }: mkCoqDerivation rec {
      pname = "noc-koika";
      defaultVersion = "0.0.1";

      opam-name = "noc";
      useDune = true;

      release."0.0.1" = {
        src = lib.const (lib.cleanSourceWith {
          src = lib.cleanSource ./.;
          filter = let inherit (lib) hasSuffix; in path: type:
            (! hasSuffix ".gitignore" path)
            && (! hasSuffix "flake.nix" path)
            && (! hasSuffix "flake.lock" path)
            && (! hasSuffix "_build" path);
        });
      };

      propagatedBuildInputs = [ koika equations metacoq];
    };

  in flake-utils.lib.eachDefaultSystem (system: let
    pkgs = import nixpkgs {
      inherit system;
      overlays = [ koika.overlays.default self.overlays.default ];
    };
  in {
    devShells.default = self.packages.${system}.default.overrideAttrs (_: {
      shellHook = ''
        alias ll="ls -lasi"
        alias spacemacs="HOME=$(pwd) emacs"
      '';
      #          shellHook = ''
      #            export XDG_CONFIG_HOME=$PWD/.config
      #            export SPACEMACSDIR=$XDG_CONFIG_HOME/spacemacs
      #
      #            if ! test -d "$XDG_CONFIG_HOME/emacs" ; then
      #              echo 'Installing spacemacs.'
      #              mkdir -p "$XDG_CONFIG_HOME"
      #              cp -Rp ${spacemacs} "$XDG_CONFIG_HOME/emacs"
      #              chmod -R u+w "$XDG_CONFIG_HOME/emacs"
      #            fi
      #
      #            test -r ~/.shellrc && . ~/.shellrc
      #          '';
    });
   packages = {
      default = self.packages.${system}.noc-koika;
      noc-koika = pkgs.coqPackages_8_18.noc-koika;
    };
  }) // {
    # NOTE: To use this flake, apply the following overlay to nixpkgs and use
    # koika from its respective coqPackages_VER attribute set!
    overlays.default = final: prev: let
      injectPkg = name: set:
        prev.${name}.overrideScope (self: _: {
          noc-koika = self.callPackage NocPkg {};
        });
    in (nixpkgs.lib.mapAttrs injectPkg {
      inherit (final) coqPackages_8_18;
    });
  };
}