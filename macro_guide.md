# 前書き (公式リソースへのリンク)

Leanのマクロシステムを扱う公式論文はここ(英):[Beyond Notations: Hygienic Macro Expansion for Theorem Proving Languages](https://arxiv.org/abs/2001.10490)。公式論文の補助コードを含むリポジトリはここ:[macro supplement](https://github.com/Kha/macro-supplement)。補助リポジトリジトリにはマクロを拡張するアルゴリズムのコード例があり、詳細に興味がある方におすすめです。

# Lean で「マクロ」ってなんでしょうか？

マクロは抽象構文木(AST)を受け新ASTを出す関数だけです。手間が省けるユースケースが多くありますが焦点となる二つは：

1. 言語の中核を拡張せずにユーザが新たな構文を作ることができるようにする
2. ユーザが反復的・間違いやすい・時間かかるタスクを自動化できるようにする

まず、Mathlib 4 の集合作記号法(set builder notation)を分かりやすい例示として調べていきたいと思います。要素が 0, 1, 2, という集合を `{0, 1, 2}` のように書きたいんだが Lean のコアも Mathlib に定義されている Set はこういう書き方を直接にサポートしていません。Mathlib に定義されている Set の API を使えば、`Set.insert 1 (Set.insert 2 (Set.singleton 3))` のように書かなければなりません。しかし、マクロを宣言するように Lean に新しい構文を認めさせ、`Set.insert..` などの仕事を自動化できます。

# マクロの扱い (Lean の立場から)

基本的に、マクロを拡張する手続きは:

1. Lean はユーザに渡されたファイルをパースし、未拡張マクロを含む AST を作り。
2. (elaboration ~> (マクロの健全処置・拡張し) ~> elaboration ...) のサイクルを繰り返し

第二ステップは未拡張マクロが出なくなるまで繰り返されます。マクロは他のマクロあるいは elaborator からの情報に頼るコードまで拡張できるので反復が必須となっております。見える通り、マクロをパース・拡張する仕事は普通のコード(マクロではないやつ)を対処する仕事とインターリーブされております。

デフォールトで Lean のマクロは健全なマクロですが、`set_option hygiene false` というコマンドで健全処置を無効出来。Lean の健全処置は公式論文で詳細が読めます。

# マクロの基本要素 (重点となる型)

大まかに言えば、ユーザが提供しないとならない成分が二つあって、それはパーサーと構文変換関数(expansion あるいは syntax transformer)です。構文変換関数って入力となるASTを変換する方法を定義する関数です。構文カテゴリー(syntax category)という三番目の成分 (`term`, `tactic`, `command` のようなやつ) もありますが、新構文カテゴリーを宣言するのは必ずしも必要ではありません。マクロの文脈で「パーサー」と言えば、`Lean.Syntax` を出す `Lean.ParserDescr` 型の要素を参照しています。 `Lean.Syntax` って Lean の構文木を表す型です。構文変換関数は `Syntax -> MacroM Syntax` 型の関数です。`Macro` という略語でもよく見えます。`MacroM` はマクロの健全処置・拡張に必要不可欠な情報を持っているモナドです。

また Mathlib の集合作記号ほうを例示として調べましょう:
```
/- 新パーサーを宣言するコマンド -/
syntax (priority := high) "{" term,+ "}" : term

/- 構文変換関数を二つ宣言します -/
macro_rules
  | `({$x}) => `(Set.singleton $x)
  | `({$x, $xs:term,*}) => `(Set.insert $x {$xs,*})

/- `Set` がインポートされたら、この二つのコマンドだけで `{1, 2, 3}` 記号が使えるようになります。 -/
```

これでマクロが最初に `Syntax` 要素を受けることのきっかけが鮮明になると思います。まず、最初の `Syntax` 引数はパーサーと一致しマクロの手続きを動かせる物です。それから、パーサーからの `Syntax` 要素はユーザーが変換して出力を作る始点になります。


`Lean.Syntax` を調査すると構文木の概念に慣れてる読者の期待通りの定義と思います。コード例に書いてあるのはちょっとだけ簡略版です(`atom`・`ident` の詳細を略しました)。この簡略化された API に合う `mkAtom`・`mkIdent` といったコンストラクターが `Lean` ネームスペースにあります。

```
inductive Syntax where
  | missing : Syntax
  | node (kind : SyntaxNodeKind) (args : Array Syntax) : Syntax
  | atom : String -> Syntax
  | ident : Name -> Syntax
```

`MacroM` は `ReaderT` で定義されます。
```
abbrev MacroM := ReaderT Macro.Context (EStateM Macro.Exception Macro.State)
```

MacroM の成分は以下のように定義されます:
```
structure Context where
  methods        : MethodsRef
  mainModule     : Name
  currMacroScope : MacroScope
  currRecDepth   : Nat := 0
  maxRecDepth    : Nat := defaultMaxRecDepth
  ref            : Syntax

inductive Exception where
  | error             : Syntax → String → Exception
  | unsupportedSyntax : Exception

structure State where
  macroScope : MacroScope
  traceMsgs  : List (Prod Name String) := List.nil
  deriving Inhabited
```

改めて重要なところを調べましょう。三つの(新構文カテゴリーが必要ではない場合、二つの)焦点となる成分は：

0. ユースケースによって、新しい構文カテゴリーを `declare_syntax_cat` で宣言し
1. `syntax` あるいは `macro` というキーワードでパーサーを宣言し
2. 構文変換関数・拡張する方法を `macro_rules` あるいは `macro` で宣言し

パーサーも構文変換関数は手動で宣言できますが、`syntax`・`macro_rules`・`macro` と伴うパターンDSLを利用するのがおすすめです。

## 構文カテゴリー・declare_syntax_cat

構文カテゴリーは quote・antiquote・パターンDSL が扱える要素の種類を表す用語です(構文カテゴリーって大体「型」に似てる概念)。`tactic`, `command`, Mathlib に定義される `bindterm` って全部構文カテゴリーです。`declare_syntax_cat` というコマンドで新しい構文カテゴリーを宣言することが出来ます。

```
set_option trace.Elab.definition true in
declare_syntax_cat binderterm

/-
上に書いてあるコマンドからの出力:

[Elab.definition.body] binderterm.quot : Lean.ParserDescr :=
Lean.ParserDescr.node `Lean.Parser.Term.quot 1024
  (Lean.ParserDescr.binary `andthen (Lean.ParserDescr.symbol "`(binderterm|")
    (Lean.ParserDescr.binary `andthen (Lean.ParserDescr.unary `incQuotDepth (Lean.ParserDescr.cat `binderterm 0))
      (Lean.ParserDescr.symbol ")")))

[Elab.definition.scc] [binderterm.quot]
-/
```

新構文カテゴリーが宣言された時点で quotation 演算子 (`` `(bindterm| ...)`` のようがあるやつ) も自動的に作られたんです。このパイプ接頭は quotation が何の構文カテゴリーの要素であるのってことを判明するための演算子で、値の型を表すアノテーションに似てる概念です。`term` と `command` がデフォールトカテゴリーにみなされるのでという構文カテゴリーはでフォールトに考えられるのでパイプ接頭が使用されません(むしろ書いていくとエラーが返されるはずです)。

## パーサー・`syntax` キーワード


パーサーは `syntax` キーワードを使って宣言出来。構文糖衣を全部見通せば `Lean.ParserDescr` ってパーサーコンビネーターで実装されますが `syntax` とパターンDSLを使ったほうがよっぽど簡単でおすすめです。`rwa` タクティック (rewrite; assumption を組み合わせるタクティック) を調べましょう:

```
/- パターン言語を使うように -/
syntax "rwa " rwRuleSeq (location)? : tactic

/-
上のパーサーってこうやって拡張されます:
[Elab.definition.body] tacticRwa__ : Lean.ParserDescr :=
Lean.ParserDescr.node `tacticRwa__ 1022
  (Lean.ParserDescr.binary `andthen
    (Lean.ParserDescr.binary `andthen (Lean.ParserDescr.nonReservedSymbol "rwa " false) Lean.Parser.Tactic.rwRuleSeq)
    (Lean.ParserDescr.unary `optional Lean.Parser.Tactic.location))

[Elab.definition.scc] [tacticRwa__]
-/

```

"rwa" ってリテラルだから二重引用符で書かれます。`rwRuleSeq` も `location` も `Lean.ParserDescr` 型の要素ですのでそのままで書けばいいんです。`:` 後のことはパーサーの構文カテゴリーを表します。`rwa` ってタクティックなんだから `: tactic` を書きます。`tacticRwa__` って自動的に作られた名前です。

パーサーに名前を手動で付ける事も出来:

```
syntax (name := introv) "introv " (colGt ident)* : tactic指定する

[Elab.definition.body] introv : Lean.ParserDescr :=
Lean.ParserDescr.node `introv 1022
  (Lean.ParserDescr.binary `andthen (Lean.ParserDescr.nonReservedSymbol "introv " false)
    (Lean.ParserDescr.unary `many
      (Lean.ParserDescr.binary `andthen (Lean.ParserDescr.const `colGt) (Lean.ParserDescr.const `ident))))

[Elab.definition.scc] [introv]
```

## マクロシステムのパターン言語

利用可能な量化子は `?` (0・１回数), `*` (0以上), `+` (1以上)です。

`?` 量化子に関する注意：Lean で `?` ってidentifierにも使える文字なのでパーサーの量化子として使いたくなる場合は丸括弧を区切り文字として書かなければなりません。例えばオプショナル `location` 要素を受けられるパーサーを書きたければ `(location)?` で書くべきです。`location?` ってはてなマークで終わる名前と一致してしまいます。

丸括弧は区切りもじで使えます。

区切られたリストは `$ts,*` で書けます(この例で `,` が区切り文字)

「extended splices」は `$[..]` のように書けます。公式論文 (p. 12) で詳細が読めます。例示は Mathlib4 のタクティックフォルダーで見えます。

リテラルは二重引用符で書けます。リテラルは pretty printer への指示として空白を語尾として持てますが、空白が果てしにないトークンと一致するのを止めません。`ParserDescr` が本物のパーサーに変換された時に、token matcher が[提供された文字列の .trim メソッドを使いますが](https://github.com/leanprover/lean4/blob/master/src/Lean/Parser/Basic.lean#L1193), 自動的に作られた formatter が[指示通りに空白を使います](https://github.com/leanprover/lean4/blob/master/src/Lean/PrettyPrinter/Formatter.lean#L328)。

## macro_rules と構文糖衣

`macro_rules` というコマンドを使って構文変換関数を宣言することが出来ます。構文変換関数は `match` 腕と似たような物です。

例:
```
macro_rules
| <パーサーが見つけた Lean.Syntax 要素> => <ユーザーに変換された出力となる Lean.Syntax 要素>
...って何列も宣言可
```

これって `Syntax -> MacroM Syntax` の `def` になります (後で調べます)。右側って失敗可能な関数なら、失敗になる場合は他のマッチが自動的に試されます。ごく最近宣言されたのは最初に試されます。

以下の例示でそのリトライ行動が見えます。それ以上、`macro_rules` を使って `macro` に宣言されたマクロに新たな構文変換関数を加えられるのも見えます。この `transitivity` (推移性) タクティックは Nat.le も Nat.le を対処できるように実装されます。最初の構文変換関数は Nat.lt の部分だからそれが最初に試されるが失敗になる場合は次の一致している変換関数が試され。
```
macro "transitivity" e:(colGt term) : tactic => `(tactic| apply Nat.le_trans (m := $e))
macro_rules
  | `(tactic| transitivity $e) => `(tactic| apply Nat.lt_trans (m := $e))

example (a b c : Nat) (h0 : a < b) (h1 : b < c) : a < c := by
transitivity b <;>
assumption

example (a b c : Nat) (h0 : a <= b) (h1 : b <= c) : a <= c := by
transitivity b <;>
assumption

/- 今回はエラーが発生してしまいますが、「最新が最初に試され」という行動が見えます。返されたエラーは `mvar1 < mvar2` に関する
　　メッセージではなく、`mvar1 <= mvar2` に関する物です。-/
example (a b c : Nat) (h0 : a <= b) (h1 : b <= c) : False := by
transitivity b <;>
assumption
```


`set_option trace.Elab.definition true in` で構文糖衣なしの定義が見えます。以下の例示は Mathlib4 の `exfalso` タクティックを調べます。
```
set_option trace.Elab.definition true in
macro "exfalso" : tactic => `(apply False.elim)

/-
拡張の出力：

[Elab.definition.body] myMacro._@._hyg.320 : Lean.Macro :=
fun x =>
  let discr := x;
  /- This is where Lean tries to actually identify that it's an invocation of the exfalso tactic -/
  if Lean.Syntax.isOfKind discr `tacticExfalso = true then
    let discr := Lean.Syntax.getArg discr 0;
    let x := discr;
    do
      /- Lean getting scope/meta info from the macro monad -/
      let info ← Lean.MonadRef.mkInfoFromRefPos
      let scp ← Lean.getCurrMacroScope
      let mainModule ← Lean.getMainModule
      pure
          (Lean.Syntax.node `Lean.Parser.Tactic.seq1
            #[Lean.Syntax.node `null
                #[Lean.Syntax.node `Lean.Parser.Tactic.apply
                    #[Lean.Syntax.atom info "apply",
                      Lean.Syntax.ident info (String.toSubstring "False.elim")
                        (Lean.addMacroScope mainModule `False.elim scp) [(`False.elim, [])]]]])
  else
    /- If this wasn't actually an invocation of the exfalso tactic, throw the "unsupportedSyntax" error -/
    let discr := x;
    throw Lean.Macro.Exception.unsupportedSyntax
-/
```

`macro_rules` を使わずに構文変換関数を手動でも書けます。そのため、パーサーに名前をつけて `@[macro myExFalsoParser]` アトリビュートで飾っていくことで `def` とパーサーを接続しなければなりません:
```
syntax (name := myExfalsoParser) "myExfalso" : tactic

-- `Macro` って `Syntax -> TacticM Unit` の略だと覚えていきましょう。
@[macro myExfalsoParser] def implMyExfalso : Macro :=
fun stx => `(tactic| apply False.elim)

example (p : Prop) (h : p) (f : p -> False) : 3 = 2 := by
myExfalso
exact f h
```

気が向いたら構文糖衣なしにも書けます:
```
syntax (name := myExfalsoParser) "myExfalso" : tactic

@[macro myExfalsoParser] def implMyExfalso : Lean.Macro :=
fun stx =>
  do
    let info ← Lean.MonadRef.mkInfoFromRefPos
    let scp ← Lean.getCurrMacroScope
    let mainModule ← Lean.getMainModule
    pure
        (Lean.Syntax.node `Lean.Parser.Tactic.apply
          #[Lean.Syntax.atom info "apply",
            Lean.Syntax.ident info (String.toSubstring "False.elim") (Lean.addMacroScope mainModule `False.elim scp)
              [(`False.elim, [])]])

example (p : Prop) (h : p) (f : p -> False) : 3 = 2 := by
myExfalso
exact f h
```

## `macro` キーワード

`macro` はユーザがパーサーも拡張も同時に作ることが出来る略語だけです。`macro_rules` を使って `macro` で宣言された拡張に新しいやつを加えられます。

# Unexpanders

申し訳ありません、この文は未完成です。Mathlib4 の Set モジュールで unexpander の例示が見えます。

# More 例示:

Mathlib4の[Tactic.Basic](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/Basic.lean)で勉強になれる例示が複数あり。

# 具体的に便利なポイント:

マクロシステムを通じるコマンドの出力・トレースは後のオプションを `true` にするように見え流ようになれます: `set_option trace.Elab.definition true`

オプションが有効されるところを限る構文もあり：`set_option ... in`

マクロの健全処置は `set_option hygiene false` を使って無効でき。
