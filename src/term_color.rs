use std::fmt::Display;

#[allow(dead_code)]
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum AnsiEscCode {
    FgBlack,
    FgRed,
    FgGreen,
    FgYellow,
    FgBlue,
    FgMagenta,
    FgCyan,
    FgWhite,
    FgBrightBlack,
    FgBrightRed,
    FgBrightGreen,
    FgBrightYellow,
    FgBrightBlue,
    FgBrightMagenta,
    FgBrightCyan,
    FgBrightWhite,
    BgBlack,
    BgRed,
    BgGreen,
    BgYellow,
    BgBlue,
    BgMagenta,
    BgCyan,
    BgWhite,
    BgBrightBlack,
    BgBrightRed,
    BgBrightGreen,
    BgBrightYellow,
    BgBrightBlue,
    BgBrightMagenta,
    BgBrightCyan,
    BgBrightWhite,

    ResetColor,
}

impl Display for AnsiEscCode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AnsiEscCode::FgBlack => write!(f, "\x1b[30m"),
            AnsiEscCode::FgRed => write!(f, "\x1b[31m"),
            AnsiEscCode::FgGreen => write!(f, "\x1b[32m"),
            AnsiEscCode::FgYellow => write!(f, "\x1b[33m"),
            AnsiEscCode::FgBlue => write!(f, "\x1b[34m"),
            AnsiEscCode::FgMagenta => write!(f, "\x1b[35m"),
            AnsiEscCode::FgCyan => write!(f, "\x1b[36m"),
            AnsiEscCode::FgWhite => write!(f, "\x1b[37m"),
            AnsiEscCode::FgBrightBlack => write!(f, "\x1b[90m"),
            AnsiEscCode::FgBrightRed => write!(f, "\x1b[91m"),
            AnsiEscCode::FgBrightGreen => write!(f, "\x1b[92m"),
            AnsiEscCode::FgBrightYellow => write!(f, "\x1b[93m"),
            AnsiEscCode::FgBrightBlue => write!(f, "\x1b[94m"),
            AnsiEscCode::FgBrightMagenta => write!(f, "\x1b[95m"),
            AnsiEscCode::FgBrightCyan => write!(f, "\x1b[96m"),
            AnsiEscCode::FgBrightWhite => write!(f, "\x1b[97m"),
            AnsiEscCode::BgBlack => write!(f, "\x1b[40m"),
            AnsiEscCode::BgRed => write!(f, "\x1b[41m"),
            AnsiEscCode::BgGreen => write!(f, "\x1b[42m"),
            AnsiEscCode::BgYellow => write!(f, "\x1b[43m"),
            AnsiEscCode::BgBlue => write!(f, "\x1b[44m"),
            AnsiEscCode::BgMagenta => write!(f, "\x1b[45m"),
            AnsiEscCode::BgCyan => write!(f, "\x1b[46m"),
            AnsiEscCode::BgWhite => write!(f, "\x1b[47m"),
            AnsiEscCode::BgBrightBlack => write!(f, "\x1b[100m"),
            AnsiEscCode::BgBrightRed => write!(f, "\x1b[101m"),
            AnsiEscCode::BgBrightGreen => write!(f, "\x1b[102m"),
            AnsiEscCode::BgBrightYellow => write!(f, "\x1b[103m"),
            AnsiEscCode::BgBrightBlue => write!(f, "\x1b[104m"),
            AnsiEscCode::BgBrightMagenta => write!(f, "\x1b[105m"),
            AnsiEscCode::BgBrightCyan => write!(f, "\x1b[106m"),
            AnsiEscCode::BgBrightWhite => write!(f, "\x1b[107m"),
            AnsiEscCode::ResetColor => write!(f, "\x1b[0m"),
        }
    }
}
