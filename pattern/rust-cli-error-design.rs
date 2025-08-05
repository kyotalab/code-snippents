// このRustファイルはClaudeによって生成された "CLIツールでのエラーハンドリングパターン" です。


use std::path::PathBuf;
use thiserror::Error;

// =============================================================================
// 1. CLIツール用エラー定義（シンプル版）
// =============================================================================

/// CLIアプリケーションの統合エラー型
#[derive(Error, Debug)]
pub enum AppError {
    // --- ユーザー入力関連エラー ---
    /// 無効な引数やオプション
    #[error("Invalid argument: {message}")]
    InvalidArgument { message: String },

    /// 必須引数の不足
    #[error("Missing required argument: {argument}")]
    MissingArgument { argument: String },

    /// 無効なファイルパス
    #[error("Invalid file path: {path}")]
    InvalidPath { path: PathBuf },

    // --- ファイル操作エラー ---
    /// ファイルが見つからない
    #[error("File not found: {path}")]
    FileNotFound { path: PathBuf },

    /// ファイル読み書きエラー
    #[error("File I/O error: {path} - {message}")]
    FileIo { path: PathBuf, message: String },

    /// ファイル形式エラー
    #[error("Invalid file format: {path} - expected {expected}, got {actual}")]
    InvalidFileFormat {
        path: PathBuf,
        expected: String,
        actual: String,
    },

    // --- データ処理エラー ---
    /// JSON解析エラー
    #[error("JSON parse error in {file}: {message}")]
    JsonParse { file: String, message: String },

    /// YAML解析エラー
    #[error("YAML parse error in {file}: {message}")]
    YamlParse { file: String, message: String },

    /// CSV解析エラー
    #[error("CSV parse error in {file}: {message}")]
    CsvParse { file: String, message: String },

    // --- 設定・環境エラー ---
    /// 設定ファイルエラー
    #[error("Configuration error: {message}")]
    Config { message: String },

    /// 環境変数エラー
    #[error("Environment variable error: {variable} - {message}")]
    Environment { variable: String, message: String },

    // --- ネットワーク・外部サービスエラー ---
    /// ネットワーク接続エラー
    #[error("Network error: {message}")]
    Network { message: String },

    /// API呼び出しエラー
    #[error("API error: {endpoint} returned {status} - {message}")]
    Api {
        endpoint: String,
        status: u16,
        message: String,
    },

    // --- 汎用エラー ---
    /// 想定外の内部エラー
    #[error("Internal error: {message}")]
    Internal { message: String },

    /// 機能未実装（開発中）
    #[error("Feature not implemented: {feature}")]
    NotImplemented { feature: String },
}

// =============================================================================
// 2. 便利なコンストラクタ関数
// =============================================================================

impl AppError {
    // --- ユーザー入力エラー ---
    pub fn invalid_argument(message: impl Into<String>) -> Self {
        Self::InvalidArgument {
            message: message.into(),
        }
    }

    pub fn missing_argument(argument: impl Into<String>) -> Self {
        Self::MissingArgument {
            argument: argument.into(),
        }
    }

    pub fn invalid_path(path: impl Into<PathBuf>) -> Self {
        Self::InvalidPath { path: path.into() }
    }

    // --- ファイル操作エラー ---
    pub fn file_not_found(path: impl Into<PathBuf>) -> Self {
        Self::FileNotFound { path: path.into() }
    }

    pub fn file_io(path: impl Into<PathBuf>, message: impl Into<String>) -> Self {
        Self::FileIo {
            path: path.into(),
            message: message.into(),
        }
    }

    pub fn invalid_file_format(
        path: impl Into<PathBuf>,
        expected: impl Into<String>,
        actual: impl Into<String>,
    ) -> Self {
        Self::InvalidFileFormat {
            path: path.into(),
            expected: expected.into(),
            actual: actual.into(),
        }
    }

    // --- データ処理エラー ---
    pub fn json_parse(file: impl Into<String>, message: impl Into<String>) -> Self {
        Self::JsonParse {
            file: file.into(),
            message: message.into(),
        }
    }

    pub fn yaml_parse(file: impl Into<String>, message: impl Into<String>) -> Self {
        Self::YamlParse {
            file: file.into(),
            message: message.into(),
        }
    }

    pub fn csv_parse(file: impl Into<String>, message: impl Into<String>) -> Self {
        Self::CsvParse {
            file: file.into(),
            message: message.into(),
        }
    }

    // --- 設定・環境エラー ---
    pub fn config(message: impl Into<String>) -> Self {
        Self::Config {
            message: message.into(),
        }
    }

    pub fn environment(variable: impl Into<String>, message: impl Into<String>) -> Self {
        Self::Environment {
            variable: variable.into(),
            message: message.into(),
        }
    }

    // --- ネットワーク・外部サービスエラー ---
    pub fn network(message: impl Into<String>) -> Self {
        Self::Network {
            message: message.into(),
        }
    }

    pub fn api(endpoint: impl Into<String>, status: u16, message: impl Into<String>) -> Self {
        Self::Api {
            endpoint: endpoint.into(),
            status,
            message: message.into(),
        }
    }

    // --- 汎用エラー ---
    pub fn internal(message: impl Into<String>) -> Self {
        Self::Internal {
            message: message.into(),
        }
    }

    pub fn not_implemented(feature: impl Into<String>) -> Self {
        Self::NotImplemented {
            feature: feature.into(),
        }
    }
}

// =============================================================================
// 3. 標準ライブラリエラーからの自動変換
// =============================================================================

impl From<std::io::Error> for AppError {
    fn from(error: std::io::Error) -> Self {
        match error.kind() {
            std::io::ErrorKind::NotFound => Self::file_not_found("unknown"),
            std::io::ErrorKind::PermissionDenied => Self::file_io("unknown", "Permission denied"),
            _ => Self::file_io("unknown", error.to_string()),
        }
    }
}

impl From<serde_json::Error> for AppError {
    fn from(error: serde_json::Error) -> Self {
        Self::json_parse("unknown", error.to_string())
    }
}

impl From<serde_yaml::Error> for AppError {
    fn from(error: serde_yaml::Error) -> Self {
        Self::yaml_parse("unknown", error.to_string())
    }
}

impl From<csv::Error> for AppError {
    fn from(error: csv::Error) -> Self {
        Self::csv_parse("unknown", error.to_string())
    }
}

// HTTP client libraries (reqwest, ureq等)
#[cfg(feature = "reqwest")]
impl From<reqwest::Error> for AppError {
    fn from(error: reqwest::Error) -> Self {
        if error.is_timeout() {
            Self::network("Request timeout")
        } else if error.is_connect() {
            Self::network("Connection failed")
        } else {
            Self::network(error.to_string())
        }
    }
}

// =============================================================================
// 4. CLIフレンドリーな機能
// =============================================================================

impl AppError {
    /// ユーザーにとって分かりやすいエラーメッセージを生成
    pub fn user_message(&self) -> String {
        match self {
            Self::InvalidArgument { .. } => {
                format!("{}\nUse --help for usage information.", self)
            }
            Self::MissingArgument { .. } => {
                format!("{}\nUse --help for usage information.", self)
            }
            Self::FileNotFound { .. } => {
                format!("{}\nPlease check the file path and try again.", self)
            }
            Self::Config { .. } => {
                format!("{}\nPlease check your configuration file.", self)
            }
            Self::Network { .. } => {
                format!("{}\nPlease check your internet connection.", self)
            }
            _ => self.to_string(),
        }
    }

    /// エラーの終了コードを返す
    pub fn exit_code(&self) -> i32 {
        match self {
            Self::InvalidArgument { .. } => 1,
            Self::MissingArgument { .. } => 1,
            Self::InvalidPath { .. } => 1,
            Self::FileNotFound { .. } => 2,
            Self::FileIo { .. } => 2,
            Self::InvalidFileFormat { .. } => 2,
            Self::JsonParse { .. } => 3,
            Self::YamlParse { .. } => 3,
            Self::CsvParse { .. } => 3,
            Self::Config { .. } => 4,
            Self::Environment { .. } => 4,
            Self::Network { .. } => 5,
            Self::Api { .. } => 5,
            Self::Internal { .. } => 99,
            Self::NotImplemented { .. } => 99,
        }
    }

    /// エラーが回復可能かどうか
    pub fn is_recoverable(&self) -> bool {
        matches!(self, Self::Network { .. } | Self::Api { .. })
    }

    /// ヘルプメッセージを表示すべきかどうか
    pub fn should_show_help(&self) -> bool {
        matches!(
            self,
            Self::InvalidArgument { .. } | Self::MissingArgument { .. }
        )
    }
}

// =============================================================================
// 5. Result型エイリアス
// =============================================================================

/// CLIアプリケーション用のResult型
pub type AppResult<T> = Result<T, AppError>;

// =============================================================================
// 6. エラーハンドリングヘルパー
// =============================================================================

/// CLIアプリケーションでの標準的なエラーハンドリング
pub fn handle_error(error: AppError) -> ! {
    eprintln!("Error: {}", error.user_message());

    if error.should_show_help() {
        eprintln!("\nFor more information, run with --help");
    }

    std::process::exit(error.exit_code());
}

/// メイン関数での使用を想定したヘルパーマクロ
#[macro_export]
macro_rules! cli_main {
    ($main_func:expr) => {
        fn main() {
            if let Err(error) = $main_func() {
                handle_error(error);
            }
        }
    };
}

// =============================================================================
// 7. 実用的なファイル操作ヘルパー
// =============================================================================

/// ファイル読み込みの安全なラッパー
pub fn read_file(path: impl Into<PathBuf>) -> AppResult<String> {
    let path = path.into();

    if !path.exists() {
        return Err(AppError::file_not_found(&path));
    }

    std::fs::read_to_string(&path).map_err(|e| AppError::file_io(&path, e.to_string()))
}

/// ファイル書き込みの安全なラッパー
pub fn write_file(path: impl Into<PathBuf>, content: &str) -> AppResult<()> {
    let path = path.into();

    // 親ディレクトリが存在しない場合は作成
    if let Some(parent) = path.parent() {
        if !parent.exists() {
            std::fs::create_dir_all(parent)
                .map_err(|e| AppError::file_io(parent, e.to_string()))?;
        }
    }

    std::fs::write(&path, content).map_err(|e| AppError::file_io(&path, e.to_string()))
}

/// JSONファイルの読み込み
pub fn read_json_file<T>(path: impl Into<PathBuf>) -> AppResult<T>
where
    T: serde::de::DeserializeOwned,
{
    let path = path.into();
    let content = read_file(&path)?;

    serde_json::from_str(&content)
        .map_err(|e| AppError::json_parse(path.display().to_string(), e.to_string()))
}

/// JSONファイルの書き込み
pub fn write_json_file<T>(path: impl Into<PathBuf>, data: &T) -> AppResult<()>
where
    T: serde::Serialize,
{
    let path = path.into();
    let content = serde_json::to_string_pretty(data)
        .map_err(|e| AppError::json_parse(path.display().to_string(), e.to_string()))?;

    write_file(path, &content)
}

// =============================================================================
// 8. clapとの統合（CLI引数解析）
// =============================================================================

#[cfg(feature = "clap")]
impl From<clap::Error> for AppError {
    fn from(error: clap::Error) -> Self {
        match error.kind() {
            clap::error::ErrorKind::MissingRequiredArgument => {
                Self::missing_argument(error.to_string())
            }
            clap::error::ErrorKind::InvalidValue => Self::invalid_argument(error.to_string()),
            _ => Self::invalid_argument(error.to_string()),
        }
    }
}

// =============================================================================
// 9. よくあるCLIパターンのヘルパー
// =============================================================================

/// 環境変数の安全な取得
pub fn get_env_var(name: &str) -> AppResult<String> {
    std::env::var(name).map_err(|_| AppError::environment(name, "Environment variable not found"))
}

/// 環境変数の取得（デフォルト値付き）
pub fn get_env_var_or_default(name: &str, default: &str) -> String {
    std::env::var(name).unwrap_or_else(|_| default.to_string())
}

/// ディレクトリの存在確認・作成
pub fn ensure_directory(path: impl Into<PathBuf>) -> AppResult<()> {
    let path = path.into();

    if !path.exists() {
        std::fs::create_dir_all(&path)
            .map_err(|e| AppError::file_io(&path, format!("Cannot create directory: {}", e)))?;
    } else if !path.is_dir() {
        return Err(AppError::invalid_path(&path));
    }

    Ok(())
}

/// ファイル拡張子のチェック
pub fn check_file_extension(path: &PathBuf, expected: &str) -> AppResult<()> {
    match path.extension().and_then(|ext| ext.to_str()) {
        Some(actual) if actual.eq_ignore_ascii_case(expected) => Ok(()),
        Some(actual) => Err(AppError::invalid_file_format(path, expected, actual)),
        None => Err(AppError::invalid_file_format(
            path,
            expected,
            "no extension",
        )),
    }
}

/// プログレスバー付きの長時間処理（indicatifライブラリ使用時）
#[cfg(feature = "indicatif")]
pub fn with_progress<T, F>(items: Vec<T>, operation: F) -> AppResult<Vec<T>>
where
    F: Fn(T) -> AppResult<T>,
{
    use indicatif::{ProgressBar, ProgressStyle};

    let pb = ProgressBar::new(items.len() as u64);
    pb.set_style(
        ProgressStyle::default_bar()
            .template("{spinner:.green} [{elapsed_precise}] [{bar:40.cyan/blue}] {pos}/{len} {msg}")
            .unwrap()
            .progress_chars("#>-"),
    );

    let mut results = Vec::new();

    for (i, item) in items.into_iter().enumerate() {
        pb.set_message(format!("Processing item {}", i + 1));

        match operation(item) {
            Ok(result) => {
                results.push(result);
                pb.inc(1);
            }
            Err(error) => {
                pb.finish_with_message("Failed");
                return Err(error);
            }
        }
    }

    pb.finish_with_message("Completed");
    Ok(results)
}

// =============================================================================
// 10. 設定ファイル管理
// =============================================================================

/// アプリケーション設定の標準的な場所を取得
pub fn get_config_dir(app_name: &str) -> AppResult<PathBuf> {
    let config_dir = if cfg!(target_os = "windows") {
        // Windows: %APPDATA%\{app_name}
        std::env::var("APPDATA")
            .map_err(|_| AppError::environment("APPDATA", "Windows APPDATA not found"))?
    } else {
        // Unix系: ~/.config/{app_name} または $XDG_CONFIG_HOME/{app_name}
        match std::env::var("XDG_CONFIG_HOME") {
            Ok(xdg_config) => xdg_config,
            Err(_) => {
                let home = std::env::var("HOME")
                    .map_err(|_| AppError::environment("HOME", "HOME directory not found"))?;
                format!("{}/.config", home)
            }
        }
    };

    Ok(PathBuf::from(config_dir).join(app_name))
}

/// 設定ファイルの読み込み
pub fn load_config<T>(app_name: &str, config_file: &str) -> AppResult<T>
where
    T: serde::de::DeserializeOwned + Default,
{
    let config_dir = get_config_dir(app_name)?;
    let config_path = config_dir.join(config_file);

    if !config_path.exists() {
        // 設定ファイルが存在しない場合はデフォルト値を返す
        return Ok(T::default());
    }

    read_json_file(config_path)
}

/// 設定ファイルの保存
pub fn save_config<T>(app_name: &str, config_file: &str, config: &T) -> AppResult<()>
where
    T: serde::Serialize,
{
    let config_dir = get_config_dir(app_name)?;
    ensure_directory(&config_dir)?;

    let config_path = config_dir.join(config_file);
    write_json_file(config_path, config)
}

// =============================================================================
// 11. ログ設定のシンプルなヘルパー
// =============================================================================

/// 簡単なログ設定（envとtracingを使用）
#[cfg(feature = "tracing")]
pub fn setup_logging() -> AppResult<()> {
    use tracing_subscriber::{EnvFilter, fmt, prelude::*};

    let env_filter = EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new("info"));

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(env_filter)
        .init();

    Ok(())
}

/// エラーのログ出力
#[cfg(feature = "tracing")]
impl AppError {
    pub fn log(&self) {
        match self {
            AppError::Internal { .. } => {
                tracing::error!("{}", self);
            }
            AppError::Network { .. } | AppError::Api { .. } => {
                tracing::warn!("{}", self);
            }
            _ => {
                tracing::info!("{}", self);
            }
        }
    }
}

// =============================================================================
// 12. 簡単な使用例
// =============================================================================

#[cfg(test)]
mod examples {
    use super::*;

    // 典型的なCLIツールのメイン関数例
    fn example_cli_main() -> AppResult<()> {
        // 引数チェック
        let args: Vec<String> = std::env::args().collect();
        if args.len() < 2 {
            return Err(AppError::missing_argument("input_file"));
        }

        // ファイル読み込み
        let input_path = &args[1];
        let content = read_file(input_path)?;

        // データ処理
        let data: serde_json::Value = serde_json::from_str(&content)?;

        // 結果出力
        println!("Processed {} successfully", input_path);
        println!("Data: {}", data);

        Ok(())
    }

    // エラーハンドリングの例
    fn example_with_error_handling() {
        cli_main!(example_cli_main);
    }

    #[test]
    fn test_error_creation() {
        let error = AppError::invalid_argument("unknown option --foo");
        assert_eq!(error.exit_code(), 1);
        assert!(error.should_show_help());

        let error = AppError::file_not_found("/nonexistent/file.txt");
        assert_eq!(error.exit_code(), 2);
        assert!(!error.should_show_help());
    }

    #[test]
    fn test_file_operations() {
        use std::fs;
        use tempfile::tempdir;

        let temp_dir = tempdir().unwrap();
        let file_path = temp_dir.path().join("test.txt");

        // ファイル書き込みテスト
        let result = write_file(&file_path, "Hello, World!");
        assert!(result.is_ok());

        // ファイル読み込みテスト
        let content = read_file(&file_path).unwrap();
        assert_eq!(content, "Hello, World!");

        // 存在しないファイルの読み込み
        let nonexistent = temp_dir.path().join("nonexistent.txt");
        let result = read_file(nonexistent);
        assert!(matches!(result, Err(AppError::FileNotFound { .. })));
    }
}

// =============================================================================
// 12. 実際のCLIツール実装例
// =============================================================================

#[cfg(test)]
mod cli_examples {
    use super::*;
    use serde::{Deserialize, Serialize};

    // 設定ファイルの例
    #[derive(Serialize, Deserialize, Debug, Default)]
    struct AppConfig {
        output_dir: String,
        max_files: usize,
        verbose: bool,
    }

    // ファイル変換ツールの例
    fn convert_files(input_dir: &str, output_dir: &str) -> AppResult<()> {
        let input_path = PathBuf::from(input_dir);
        let output_path = PathBuf::from(output_dir);

        // 入力ディレクトリの存在確認
        if !input_path.exists() {
            return Err(AppError::file_not_found(input_path));
        }

        // 出力ディレクトリの作成
        ensure_directory(&output_path)?;

        // ファイル一覧取得
        let entries = std::fs::read_dir(&input_path)
            .map_err(|e| AppError::file_io(&input_path, e.to_string()))?;

        let mut processed = 0;

        for entry in entries {
            let entry = entry.map_err(|e| AppError::file_io(&input_path, e.to_string()))?;
            let file_path = entry.path();

            // JSON ファイルのみ処理
            if file_path.extension().and_then(|s| s.to_str()) == Some("json") {
                process_json_file(&file_path, &output_path)?;
                processed += 1;
            }
        }

        println!("Successfully processed {} JSON files", processed);
        Ok(())
    }

    fn process_json_file(input: &PathBuf, output_dir: &PathBuf) -> AppResult<()> {
        // JSON ファイル読み込み
        let data: serde_json::Value = read_json_file(input)?;

        // 何らかの変換処理（例：prettify）
        let pretty_content = serde_json::to_string_pretty(&data)
            .map_err(|e| AppError::json_parse(input.display().to_string(), e.to_string()))?;

        // 出力ファイル名を決定
        let output_file = output_dir.join(
            input
                .file_name()
                .ok_or_else(|| AppError::invalid_path(input))?,
        );

        // 変換結果を保存
        write_file(output_file, &pretty_content)?;

        Ok(())
    }

    // コマンドライン引数処理の例（clapライブラリ使用）
    #[cfg(feature = "clap")]
    fn parse_cli_args() -> AppResult<CliArgs> {
        use clap::{Arg, Command};

        let matches = Command::new("file-converter")
            .version("1.0")
            .about("Convert JSON files")
            .arg(
                Arg::new("input")
                    .short('i')
                    .long("input")
                    .value_name("DIR")
                    .help("Input directory")
                    .required(true),
            )
            .arg(
                Arg::new("output")
                    .short('o')
                    .long("output")
                    .value_name("DIR")
                    .help("Output directory")
                    .required(true),
            )
            .arg(
                Arg::new("verbose")
                    .short('v')
                    .long("verbose")
                    .action(clap::ArgAction::SetTrue)
                    .help("Enable verbose output"),
            )
            .try_get_matches()?;

        Ok(CliArgs {
            input_dir: matches.get_one::<String>("input").unwrap().clone(),
            output_dir: matches.get_one::<String>("output").unwrap().clone(),
            verbose: matches.get_flag("verbose"),
        })
    }

    #[derive(Debug)]
    struct CliArgs {
        input_dir: String,
        output_dir: String,
        verbose: bool,
    }

    // メイン関数の例
    fn example_main() -> AppResult<()> {
        // ログ設定
        #[cfg(feature = "tracing")]
        setup_logging()?;

        // 設定ファイル読み込み
        let config: AppConfig = load_config("file-converter", "config.json")?;

        // コマンドライン引数解析
        #[cfg(feature = "clap")]
        let args = parse_cli_args()?;

        #[cfg(not(feature = "clap"))]
        let args = {
            let args: Vec<String> = std::env::args().collect();
            if args.len() < 3 {
                return Err(AppError::missing_argument("input and output directories"));
            }
            CliArgs {
                input_dir: args[1].clone(),
                output_dir: args[2].clone(),
                verbose: args.contains(&"--verbose".to_string()),
            }
        };

        if args.verbose {
            println!("Config: {:?}", config);
            println!("Args: {:?}", args);
        }

        // メイン処理
        convert_files(&args.input_dir, &args.output_dir)?;

        Ok(())
    }

    // エラーハンドリング付きメイン関数
    fn main_with_error_handling() {
        if let Err(error) = example_main() {
            #[cfg(feature = "tracing")]
            error.log();

            handle_error(error);
        }
    }

    #[test]
    fn test_cli_example() {
        use tempfile::tempdir;

        // テンポラリディレクトリ作成
        let temp_dir = tempdir().unwrap();
        let input_dir = temp_dir.path().join("input");
        let output_dir = temp_dir.path().join("output");

        // 入力ディレクトリとサンプルJSONファイル作成
        std::fs::create_dir_all(&input_dir).unwrap();

        let sample_json = serde_json::json!({
            "name": "test",
            "value": 42,
            "items": ["a", "b", "c"]
        });

        let input_file = input_dir.join("test.json");
        write_json_file(&input_file, &sample_json).unwrap();

        // 変換処理実行
        let result = convert_files(input_dir.to_str().unwrap(), output_dir.to_str().unwrap());

        assert!(result.is_ok());

        // 出力ファイルの確認
        let output_file = output_dir.join("test.json");
        assert!(output_file.exists());

        let output_content = read_file(&output_file).unwrap();
        assert!(output_content.contains("\"name\": \"test\""));
    }

    #[test]
    fn test_config_management() {
        use tempfile::tempdir;

        let temp_dir = tempdir().unwrap();
        let app_name = "test-app";

        // 環境変数を一時的に設定
        unsafe { std::env::set_var("XDG_CONFIG_HOME", temp_dir.path()) };

        let config = AppConfig {
            output_dir: "/tmp/output".to_string(),
            max_files: 100,
            verbose: true,
        };

        // 設定保存
        let result = save_config(app_name, "config.json", &config);
        assert!(result.is_ok());

        // 設定読み込み
        let loaded_config: AppConfig = load_config(app_name, "config.json").unwrap();
        assert_eq!(loaded_config.output_dir, config.output_dir);
        assert_eq!(loaded_config.max_files, config.max_files);
        assert_eq!(loaded_config.verbose, config.verbose);

        // 環境変数をクリア
        unsafe { std::env::remove_var("XDG_CONFIG_HOME") };
    }
}

// =============================================================================
// 13. Cargo.tomlの推奨設定
// =============================================================================

/// 推奨する Cargo.toml 設定:
///
/// ```toml
/// [dependencies]
/// thiserror = "1.0"
/// serde = { version = "1.0", features = ["derive"] }
/// serde_json = "1.0"
///
/// # オプション機能
/// clap = { version = "4.0", optional = true }
/// serde_yaml = { version = "0.9", optional = true }
/// csv = { version = "1.2", optional = true }
/// reqwest = { version = "0.11", features = ["json"], optional = true }
/// tracing = { version = "0.1", optional = true }
/// tracing-subscriber = { version = "0.3", optional = true }
/// indicatif = { version = "0.17", optional = true }
///
/// [dev-dependencies]
/// tempfile = "3.0"
///
/// [features]
/// default = ["clap"]
/// full = ["clap", "serde_yaml", "csv", "reqwest", "tracing", "indicatif"]
/// cli = ["clap"]
/// formats = ["serde_yaml", "csv"]
/// http = ["reqwest"]
/// logging = ["tracing", "tracing-subscriber"]
/// progress = ["indicatif"]
/// ```

// =============================================================================
// 14. よくあるエラーパターンとその対処法
// =============================================================================

/// CLIツールでよくあるエラーパターンとその対処法
pub mod error_patterns {
    use super::*;

    /// ファイルが存在しない場合の親切なエラーメッセージ
    pub fn file_not_found_with_suggestions(path: &PathBuf) -> AppError {
        let mut message = format!("File not found: {}", path.display());

        // 似たような名前のファイルを提案
        if let Some(parent) = path.parent() {
            if let Ok(entries) = std::fs::read_dir(parent) {
                let target_name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
                let mut suggestions = Vec::new();

                for entry in entries.flatten() {
                    if let Some(name) = entry.file_name().to_str() {
                        if name.contains(target_name) || target_name.contains(name) {
                            suggestions.push(name.to_string());
                        }
                    }
                }

                if !suggestions.is_empty() {
                    message.push_str(&format!("\nDid you mean: {}", suggestions.join(", ")));
                }
            }
        }

        AppError::FileNotFound { path: path.clone() }
    }

    /// 権限エラーの詳細説明
    pub fn permission_denied_with_help(path: &PathBuf, operation: &str) -> AppError {
        let message = match operation {
            "read" => format!(
                "Permission denied reading '{}'. Try:\n  sudo chmod +r {}",
                path.display(),
                path.display()
            ),
            "write" => format!(
                "Permission denied writing to '{}'. Try:\n  sudo chmod +w {}",
                path.display(),
                path.display()
            ),
            _ => format!(
                "Permission denied for {} on '{}'",
                operation,
                path.display()
            ),
        };

        AppError::file_io(path, message)
    }

    /// ディスク容量不足エラー
    pub fn disk_full_error(path: &PathBuf) -> AppError {
        AppError::file_io(path, "Disk full. Please free up space and try again.")
    }

    /// ネットワークエラーのリトライ提案
    pub fn network_error_with_retry(endpoint: &str, attempt: u32) -> AppError {
        if attempt >= 3 {
            AppError::network(format!(
                "Failed to connect to {} after {} attempts. Please check your internet connection.",
                endpoint, attempt
            ))
        } else {
            AppError::network(format!(
                "Connection to {} failed (attempt {}). Retrying...",
                endpoint, attempt
            ))
        }
    }
}

// =============================================================================
// 15. 実用的なマクロとヘルパー
// =============================================================================

/// よく使う操作のマクロ
#[macro_export]
macro_rules! ensure {
    ($condition:expr, $error:expr) => {
        if !($condition) {
            return Err($error);
        }
    };
}

#[macro_export]
macro_rules! ensure_file_exists {
    ($path:expr) => {
        ensure!($path.exists(), AppError::file_not_found($path))
    };
}

#[macro_export]
macro_rules! ensure_dir_exists {
    ($path:expr) => {
        ensure!($path.is_dir(), AppError::invalid_path($path))
    };
}

/// デバッグ情報付きエラー
#[macro_export]
macro_rules! debug_error {
    ($error:expr, $($key:expr => $value:expr),*) => {
        {
            #[cfg(debug_assertions)]
            {
                eprintln!("Debug error context:");
                $(
                    eprintln!("  {}: {}", $key, $value);
                )*
            }
            $error
        }
    };
}

// =============================================================================
// 16. テンプレート実装
// =============================================================================

/// 新しいCLIツールプロジェクトのテンプレート
pub mod template {
    use super::*;

    /// 基本的なCLI構造
    pub fn basic_cli_template() -> String {
        r#"
use cli_errors::{AppResult, AppError, handle_error};

fn main() {
    if let Err(error) = run() {
        handle_error(error);
    }
}

fn run() -> AppResult<()> {
    // コマンドライン引数の処理
    let args: Vec<String> = std::env::args().collect();

    match args.get(1).map(|s| s.as_str()) {
        Some("--version") | Some("-V") => {
            println!("{} {}", env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"));
        }
        Some("--help") | Some("-h") => {
            print_help();
        }
        Some(command) => {
            execute_command(command)?;
        }
        None => {
            return Err(AppError::missing_argument("command"));
        }
    }

    Ok(())
}

fn execute_command(command: &str) -> AppResult<()> {
    match command {
        "process" => {
            // 何らかの処理
            println!("Processing...");
            Ok(())
        }
        _ => {
            Err(AppError::invalid_argument(format!("Unknown command: {}", command)))
        }
    }
}

fn print_help() {
    println!("Usage: {} <command>", env!("CARGO_PKG_NAME"));
    println!("");
    println!("Commands:");
    println!("  process    Process files");
    println!("  --help     Show this help");
    println!("  --version  Show version");
}
"#
        .to_string()
    }
}

/// 使用例の完全なサンプル
#[cfg(test)]
mod complete_example {
    use super::*;

    // 完全なファイル処理CLIツールの例
    fn file_processor_main() -> AppResult<()> {
        let args: Vec<String> = std::env::args().collect();

        if args.len() < 2 {
            println!("Usage: {} <input-file> [output-file]", args[0]);
            return Err(AppError::missing_argument("input-file"));
        }

        let input_file = PathBuf::from(&args[1]);
        let output_file = if args.len() > 2 {
            PathBuf::from(&args[2])
        } else {
            input_file.with_extension("processed.json")
        };

        // ファイル存在確認
        ensure_file_exists!(input_file);

        // 拡張子チェック
        check_file_extension(&input_file, "json")?;

        // ファイル処理
        process_file(&input_file, &output_file)?;

        println!(
            "Successfully processed {} -> {}",
            input_file.display(),
            output_file.display()
        );

        Ok(())
    }

    fn process_file(input: &PathBuf, output: &PathBuf) -> AppResult<()> {
        // JSON読み込み
        let data: serde_json::Value = read_json_file(input)?;

        // 何らかの変換処理
        let processed = transform_data(data)?;

        // 結果保存
        write_json_file(output, &processed)?;

        Ok(())
    }

    fn transform_data(mut data: serde_json::Value) -> AppResult<serde_json::Value> {
        // 例: タイムスタンプを追加
        if let Some(obj) = data.as_object_mut() {
            obj.insert(
                "processed_at".to_string(),
                serde_json::Value::String(
                    std::time::SystemTime::now()
                        .duration_since(std::time::UNIX_EPOCH)
                        .unwrap()
                        .as_secs()
                        .to_string(),
                ),
            );
        }

        Ok(data)
    }

    #[test]
    fn test_complete_example() {
        use tempfile::tempdir;

        let temp_dir = tempdir().unwrap();
        let input_file = temp_dir.path().join("input.json");
        let output_file = temp_dir.path().join("output.json");

        // テストデータ作成
        let test_data = serde_json::json!({
            "name": "test",
            "value": 42
        });

        write_json_file(&input_file, &test_data).unwrap();

        // 処理実行
        let result = process_file(&input_file, &output_file);
        assert!(result.is_ok());

        // 結果確認
        let output_data: serde_json::Value = read_json_file(&output_file).unwrap();
        assert!(output_data.get("processed_at").is_some());
        assert_eq!(output_data.get("name").unwrap(), "test");
    }
}
