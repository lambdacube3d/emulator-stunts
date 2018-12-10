let
  config = {
    packageOverrides = pkgs: rec {
      haskellPackages = pkgs.haskellPackages.override {
        overrides = haskellPackagesNew: haskellPackagesOld: rec {
          project =
            haskellPackagesNew.callPackage ./project.nix { };

          hdis86 =
            haskellPackagesNew.callPackage ./hdis86.nix { };
        };
      };
    };
  };

  pkgs = import <nixpkgs> { inherit config; };

in
  { project = pkgs.haskellPackages.project;
  }


