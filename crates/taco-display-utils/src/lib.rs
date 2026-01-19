//! This crate contains utility functions for displaying iterators and
//! types in a nice and structured way.

use std::fmt::Display;

/// Size of a tab when displaying types
pub const TAB_SIZE: usize = 4;

/// Join iterators over string types using the given separator
///
/// This function can be used to join iterators over string types using the
/// given separator. The separator can be any string, including an empty string.
/// It will not be appended to the end of the result.
///
/// # Example
///
/// ```
/// use taco_display_utils::join_iterator;
///
/// let list = vec!["a", "b", "c"];
/// assert_eq!(join_iterator(list.iter(), ", "), "a, b, c");
/// ```
pub fn join_iterator<T: ToString + Sized, U: Iterator<Item = T>, S: Into<String>>(
    list: U,
    sep: S,
) -> String {
    list.map(|x| x.to_string())
        .collect::<Vec<_>>()
        .join(sep.into().as_str())
}

/// Join iterators over string types using the given separator and add separator
/// at the end
///
/// This function can be used to join iterators over string types using the
/// given separator. The separator can be any string, including an empty string.
/// It will also be appended to the end of the resulting string, except if the
/// string is empty.
///
/// # Example
///
/// ```
/// use taco_display_utils::join_iterator_and_add_back;
///
/// let list = vec!["a", "b", "c"];
/// assert_eq!(join_iterator_and_add_back(list.iter(), ", "), "a, b, c, ");
///
/// let list: Vec<&str> = vec![];
/// assert_eq!(join_iterator_and_add_back(list.iter(), ", "), "");
/// ```
pub fn join_iterator_and_add_back<T: ToString + Sized, U: Iterator<Item = T>, S: Into<String>>(
    list: U,
    sep: S,
) -> String {
    let sep = sep.into();

    let res = join_iterator(list, &sep);

    if res.is_empty() {
        return res;
    }

    res + &sep
}

/// This function can be used to display an iterator in a stable order
///
/// # Example
///
/// ```
/// use taco_display_utils::display_iterator_stable_order;
///
/// let list = vec!["c", "a", "b"];
/// assert_eq!(display_iterator_stable_order(list.iter()), "a, b, c");
/// ```
pub fn display_iterator_stable_order<T: Display>(set: impl IntoIterator<Item = T>) -> String {
    let mut sorted_set = set.into_iter().collect::<Vec<_>>();
    sorted_set.sort_by_key(|a| a.to_string());
    join_iterator(sorted_set.iter(), ", ")
}

/// This function can be used to indent all lines of a string by a tab size
///
/// # Example
///
/// ```
/// use taco_display_utils::indent_all;
///
/// let input = "a\nb\nc";
/// assert_eq!(indent_all(input), "    a\n    b\n    c");
/// ```
pub fn indent_all<S>(input: S) -> String
where
    S: Into<String>,
{
    let tab = " ".repeat(TAB_SIZE);
    let input: String = input.into();
    let input_n_lines = input.lines().count();

    let mut output = String::with_capacity(input.len() + input_n_lines * TAB_SIZE);

    for (i, line) in input.lines().enumerate() {
        if !line.is_empty() {
            output.push_str(&tab);
        }

        output.push_str(line);

        if i != input_n_lines - 1 {
            output.push('\n');
        }
    }

    if input.ends_with('\n') {
        output.push('\n');
    }

    output
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_join_iterator() {
        let list = ["a", "b", "c"];
        assert_eq!(join_iterator(list.iter(), ", "), "a, b, c");
    }

    #[test]
    fn test_join_iterator_and_add_back() {
        let list = ["a", "b", "c"];
        assert_eq!(join_iterator_and_add_back(list.iter(), ", "), "a, b, c, ");

        let list: Vec<&str> = vec![];
        assert_eq!(join_iterator_and_add_back(list.iter(), ", "), "");
    }

    #[test]
    fn test_display_iterator_stable_order() {
        let list = ["c", "a", "b"];
        assert_eq!(display_iterator_stable_order(list.iter()), "a, b, c");
    }

    #[test]
    fn test_indent_all() {
        let input = "a\nb\nc";
        assert_eq!(indent_all(input), "    a\n    b\n    c");

        let input = "a\nb\nc\n";
        assert_eq!(indent_all(input), "    a\n    b\n    c\n");
    }
}
