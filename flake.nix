{
  description = "Lean 4 FFI project with C++ glob support";

  inputs = {
    nixpkgs.url = "nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    # lean.url = "github:leanprover/lean4";
  };

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
      # lean,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
          # overlays = [ lean.overlay ];
        };

        # For building .so: libc++, gmp, uv, etc.
        buildInputs = with pkgs; [
          # lean.packages.lean
          # lake
          clang
          llvm
          libuv
          gmp
          zlib
          libcxx
          # libcxxabi
        ];

        # Needed for correct linkage of C++ standard library
        envVars = {
          CXX = "clang++";
          CC = "clang";
          CXXFLAGS = "-stdlib=libc++";
          LDFLAGS = "-lc++ -lc++abi";
          LD_LIBRARY_PATH = pkgs.lib.makeLibraryPath buildInputs;
        };

      in
      {
        devShells.default = pkgs.mkShell {
          inherit buildInputs;
          shellHook = ''
            echo "🧠 Lean dev shell ready"
            export ${builtins.concatStringsSep " " (builtins.attrValues envVars)}
          '';
        };
        # packages.default = pkgs.stdenv.mkDerivation {
        #   name = "lean-glob-posix";
        #   src = ./.;
        #   buildInputs = buildInputs;
        #   configurePhase = "true";
        #   buildPhase = ''
        #     lake build
        #   '';
        #   installPhase = ''
        #     mkdir -p $out
        #     cp -r .lake/build $out/
        #   '';
        # };
      }
    );
}
