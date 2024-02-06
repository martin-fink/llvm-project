{
  description = "A template for Nix based C++ project setup.";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/23.05";

    utils.url = "github:numtide/flake-utils";
    utils.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs = { self, nixpkgs, ... }@inputs: inputs.utils.lib.eachSystem [
    "x86_64-linux"
    "aarch64-linux"
    "x86_64-darwin"
    "aarch64-darwin"
  ]
    (system:
      let
        pkgs = import nixpkgs {
          inherit system;
        };
      in
      {
        devShell = pkgs.mkShell rec {
          name = "llvm dev env";

          packages = with pkgs; [
            # Development Tools
            ccache
            gdb
            cmake
            ninja
            graphviz
            llvmPackages_latest.lldb
            pkg-config
            mold
            clang
            zlib
            lit
          ];

          NIX_LDFLAGS = "-rpath ${pkgs.zlib}/lib";
        };
      });
}

