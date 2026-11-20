{
  description = "Algebra of Programming in Agda";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  outputs = { self, nixpkgs }:
    let each = nixpkgs.lib.genAttrs [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" ];
    in {
      devShells = each (s: { default = nixpkgs.legacyPackages.${s}.mkShell {
        packages = [ nixpkgs.legacyPackages.${s}.agda ];
      }; });
      checks = each (s: let pkgs = nixpkgs.legacyPackages.${s}; in {
        tex-printer-domain = pkgs.runCommand "tex-printer-domain" { nativeBuildInputs = [ pkgs.python3 ]; } ''
          python3 ${./checks/tex_printer_domain.py} > $out
        '';
        proofs = pkgs.runCommand "aop-proofs" { nativeBuildInputs = [ pkgs.agda ]; } ''
          cp -r ${./src} src
          chmod -R u+w src
          agda --safe --without-K --no-libraries -i src src/Everything.agda
          touch $out
        '';
      });
    };
}
