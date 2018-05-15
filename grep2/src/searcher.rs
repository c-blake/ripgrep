#[derive(Debug)]
struct Options {
    /// The line terminator to use.
    lineterm: u8,
    /// Whether to invert matching.
    invert_match: bool,
    /// Whether to quit searching after a match is found.
    stop_after_first_match: bool,
    /// The number of lines after a match to include.
    after_context: usize,
    /// The number of lines before a match to include.
    before_context: usize,
    /// Whether to report absolute byte offsets or not.
    absolute_byte_offset: bool,
    /// Whether to count line numbers.
    line_number: bool,
    /// Whether to enable binary data detection.
    /// TODO: This should probably be an enum.
    binary: bool,
}
