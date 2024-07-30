{
  inputs = { nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable"; };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let pkgs = nixpkgs.legacyPackages.${system};
      in {
        devShell = pkgs.mkShell {
          buildInputs =
            [ pkgs.rustup pkgs.rustc pkgs.rust-analyzer pkgs.rustic-rs ];
          shellHook = ''
            rustup toolchain add stable
            rustup override set stable
          '';
        };
      });
}
