nix-shell -p 'haskellPackages.ghcWithPackages (pkgs: [pkgs.QuickCheck pkgs.ghcid pkgs.brittany pkgs.stylish-haskell])'
