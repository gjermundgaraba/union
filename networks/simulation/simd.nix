_: {
  perSystem =
    {
      pkgs,
      goPkgs,
      self',
      crane,
      system,
      ensureAtRepositoryRoot,
      ...
    }:
    {
      packages = {
        simd = goPkgs.pkgsStatic.buildGoModule (
          {
            name = "simd";
            # src = builtins.fetchGit {
            #   url = "git@github.com:unionlabs/wasmd.git";
            #   rev = "a2e7048bbdd43206c69fb9353c6aff219aecefda";
            # };
            src = pkgs.fetchFromGitHub {
              owner = "unionlabs";
              repo = "wasmd";
              # rev = "wasm-clients-v0.50.0";
              rev = "a2e7048bbdd43206c69fb9353c6aff219aecefda";
              sha256 = "sha256-b0JPYyk7VhuaEAeQmrbAU6i1UO242oV1DzW8QjOFIak=";
            };
            vendorHash = null;
            doCheck = false;
            doInstallCheck = false;
            meta.mainProgram = "wasmd";
            # CGO_ENABLED = 0;
          }
          // (
            let
              libwasmvm = self'.packages.libwasmvm-1_5_0;
            in
            if pkgs.stdenv.isLinux then
              {
                # Statically link if we're on linux
                nativeBuildInputs = [
                  pkgs.musl
                  libwasmvm
                ];
                ldflags = [
                  "-linkmode external"
                  "-extldflags '-z noexecstack -static -L${pkgs.musl}/lib -L${libwasmvm}/lib'"
                ];
              }
            # else if pkgs.stdenv.isDarwin then {
            #   # Dynamically link if we're on darwin by wrapping the program
            #   # such that the DYLD_LIBRARY_PATH includes libwasmvm
            #   buildInputs = [ pkgs.makeWrapper libwasmvm ];
            #   postFixup = ''
            #     wrapProgram $out/bin/wasmd \
            #     --set DYLD_LIBRARY_PATH ${(pkgs.lib.makeLibraryPath [ libwasmvm ])};
            #   '';
            # } else
            else
              { }
          )
        );

        simd-image = pkgs.dockerTools.buildImage {
          name = "simd";

          copyToRoot = pkgs.buildEnv {
            name = "image-root";
            paths = [
              pkgs.coreutils-full
              pkgs.cacert
            ];
            pathsToLink = [ "/bin" ];
          };
          config = {
            Entrypoint = [ (pkgs.lib.getExe self'.packages.simd) ];
            Env = [ "SSL_CERT_FILE=${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt" ];
          };
        };
      };
    };
}
