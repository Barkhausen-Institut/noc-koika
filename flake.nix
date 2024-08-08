{
  inputs = {
    nixpkgs.follows = "koika/nixpkgs";
    flake-utils.url = github:numtide/flake-utils;
    koika.url = github:Barkhausen-Institut/koika/master;
  };
  outputs = { self, nixpkgs, flake-utils, koika }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ koika.overlays.default ];
        };
        ocamlPackages = pkgs.ocaml-ng.ocamlPackages_4_12;

        coq = pkgs.coq_8_14.override {
          customOCamlPackages = ocamlPackages;
        };
        coqPackages = pkgs.coqPackages_8_14.overrideScope'
          (self: super: {
            coq = coq;
          });
        NocPkg = { lib, mkCoqDerivation, coq, equations, koika }: mkCoqDerivation rec {
          pname = "noc-koika";
          version = "0.0.1";

          opam-name = "noc-koika";
          useDune = true;

          revision."8.14" = {
            inherit src;
          };

          src = lib.cleanSourceWith {
            src = lib.cleanSource ./.;
            filter = let inherit (lib) hasSuffix; in path: type:
              (! hasSuffix ".gitignore" path)
              && (! hasSuffix "flake.nix" path)
              && (! hasSuffix "flake.lock" path)
              && (! hasSuffix "_build" path);
          };

          propagatedBuildInputs = [ koika equations ];
        };
      in
      {
        packages.default = self.packages.${system}.noc-koika;
        packages.noc-koika = pkgs.coqPackages_8_14.callPackage NocPkg {};
        devShells.default = pkgs.mkShell {
          inputsFrom = [ pkgs.coqPackages_8_14.koika ];
          packages =
            [ pkgs.coqPackages_8_14.koika ]
            ++
            (with coqPackages; [
              equations metacoq
            ]);

          shellHook = ''
            alias ll="ls -lasi"
            alias spacemacs="HOME=$(pwd) emacs"
          '';
        };
      }
    );
}
