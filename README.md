# README

Files should verify using the [Dafny extension](https://marketplace.visualstudio.com/items?itemName=correctnessLab.dafny-vscode) on [Visual Studio Code](https://code.visualstudio.com),
using the following options:

```json
{
  "dafny.serverVerifyArguments": [
      "/timeLimit:30",
      "/autoTriggers:1",
      "/z3opt:nlsat.randomize=false",
      "/warnShadowing",
      "/ironDafny",
      "/allowGlobals",
      "/z3opt:pi.warnings=true",
      "/proverWarnings:1",
  ]
}
```
