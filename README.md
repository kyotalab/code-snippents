# Code Snippets

プログラマー脳の概念に基づいて、コードの知識チャンクを体系的に管理するためのリポジトリです。

## 📁 構造

```
code-snippets/
├── syntax/     # 言語固有の構文、文法パターン
├── pattern/    # デザインパターン、アーキテクチャパターン
├── algorithm/  # アルゴリズム、データ構造の実装
├── concept/    # プログラミング概念、理論的知識
├── technique/  # 実装テクニック、ベストプラクティス
└── util/       # ユーティリティ関数、ヘルパー関数
```

## 🏷️ タグ体系

各スニペットは以下のようなタグで分類されています：

- **言語**: `rust`, `go`, `python`, `javascript`, etc.
- **技術**: `aws`, `docker`, `kubernetes`, `terraform`, etc.
- **領域**: `web`, `cli`, `api`, `database`, etc.

## 📝 スニペット形式

各スニペットは以下の形式で管理されています：

```markdown
---
id: 20241201120000
title: Option型の基本的な使い方
type: syntax
tags: [rust, error-handling]
created: 2024-12-01 12:00:00
updated: 2024-12-01 12:00:00
---

内容...
```

## 🔍 検索方法

### タグで検索

```bash
# Rust関連のスニペットを検索
grep -r "tags:.*rust" .

# AWS関連のパターンを検索
grep -r "tags:.*aws" pattern/
```

### 内容で検索

```bash
# ripgrepを使用（推奨）
rg "Option" --type md

# grepを使用
grep -r "Option" . --include="*.md"
```

## ⚡ Vim統合

Neovimでの快適な作成・編集のため、以下のキーマップを設定：

```lua
-- syntax snippet
vim.keymap.set("n", "<leader>cns", function()
  create_snippet_note("syntax")
end, { desc = "New syntax snippet" })

-- pattern snippet
vim.keymap.set("n", "<leader>cnp", function()
  create_snippet_note("pattern")
end, { desc = "New pattern snippet" })

-- 他のキーマップ...
```

## 📊 統計

- 総スニペット数: XXX件
- 対応言語: Rust, Go, Python, JavaScript, TypeScript
- 主要技術: AWS, Docker, Kubernetes

## 🤝 コントリビューション

個人用リポジトリですが、有用なスニペットがあれば Issue や PR でお知らせください。

## 📄 ライセンス

MIT License
