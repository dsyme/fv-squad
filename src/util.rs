//! This module contains a collection of various tools to use to manipulate
//! and control messages and data associated with raft.

// Copyright 2019 TiKV Project Authors. Licensed under Apache-2.0.

use std::fmt;
#[cfg(not(feature = "aeneas"))]
use std::fmt::Write;

#[cfg(not(feature = "aeneas"))]
use slog::{OwnedKVList, Record, KV};

use crate::eraftpb::{Entry, Message};
use crate::HashSet;
use raft_proto::protocompat::*;

#[cfg(not(feature = "aeneas"))]
use slog::{b, record_static};

/// A number to represent that there is no limit.
pub const NO_LIMIT: u64 = u64::MAX;

/// Truncates the list of entries down to a specific byte-length of
/// all entries together.
///
/// # Examples
///
/// ```
/// use raft::{util::limit_size, prelude::*};
///
/// let template = {
///     let mut entry = Entry::default();
///     entry.data = "*".repeat(100).into_bytes().into();
///     entry
/// };
///
/// // Make a bunch of entries that are ~100 bytes long
/// let mut entries = vec![
///     template.clone(),
///     template.clone(),
///     template.clone(),
///     template.clone(),
///     template.clone(),
/// ];
///
/// assert_eq!(entries.len(), 5);
/// limit_size(&mut entries, Some(220));
/// assert_eq!(entries.len(), 2);
///
/// // `entries` will always have at least 1 Message
/// limit_size(&mut entries, Some(0));
/// assert_eq!(entries.len(), 1);
/// ```
pub fn limit_size<T: PbMessage + Clone>(entries: &mut Vec<T>, max: Option<u64>) {
    if entries.len() <= 1 {
        return;
    }
    let max = match max {
        None | Some(NO_LIMIT) => return,
        Some(max) => max,
    };

    let mut size = 0;
    let limit = entries
        .iter()
        .take_while(|&e| {
            if size == 0 {
                size += u64::from(e.compute_size());
                return true;
            }
            size += u64::from(e.compute_size());
            size <= max
        })
        .count();

    entries.truncate(limit);
}

/// Check whether the entry is continuous to the message.
/// i.e msg's next entry index should be equal to the index of the first entry in `ents`
pub fn is_continuous_ents(msg: &Message, ents: &[Entry]) -> bool {
    if !msg.entries.is_empty() && !ents.is_empty() {
        let expected_next_idx = msg.entries.last().unwrap().index + 1;
        return expected_next_idx == ents.first().unwrap().index;
    }
    true
}

#[cfg(not(feature = "aeneas"))]
struct FormatKeyValueList {
    pub buffer: String,
}

#[cfg(not(feature = "aeneas"))]
impl slog::Serializer for FormatKeyValueList {
    fn emit_arguments(&mut self, key: slog::Key, val: &fmt::Arguments) -> slog::Result {
        if !self.buffer.is_empty() {
            write!(&mut self.buffer, ", {key}: {val}").unwrap();
        } else {
            write!(&mut self.buffer, "{key}: {val}").unwrap();
        }
        Ok(())
    }
}

#[cfg(not(feature = "aeneas"))]
pub(crate) fn format_kv_list(kv_list: &OwnedKVList) -> String {
    let mut formatter = FormatKeyValueList {
        buffer: "".to_owned(),
    };
    let record = record_static!(slog::Level::Trace, "");
    kv_list
        .serialize(
            &Record::new(&record, &format_args!(""), b!()),
            &mut formatter,
        )
        .unwrap();
    formatter.buffer
}

/// Get the majority number of given nodes count.
#[inline]
pub fn majority(total: usize) -> usize {
    (total / 2) + 1
}

/// A convenient struct that handles queries to both HashSet.
pub struct Union<'a> {
    first: &'a HashSet<u64>,
    second: &'a HashSet<u64>,
}

impl<'a> Union<'a> {
    /// Creates a union.
    pub fn new(first: &'a HashSet<u64>, second: &'a HashSet<u64>) -> Union<'a> {
        Union { first, second }
    }

    /// Checks if id shows up in either HashSet.
    #[inline]
    pub fn contains(&self, id: u64) -> bool {
        self.first.contains(&id) || self.second.contains(&id)
    }

    /// Returns an iterator iterates the distinct values in two sets.
    pub fn iter(&self) -> impl Iterator<Item = u64> + '_ {
        self.first.union(self.second).cloned()
    }

    /// Checks if union is empty.
    pub fn is_empty(&self) -> bool {
        self.first.is_empty() && self.second.is_empty()
    }

    /// Gets the count of the union.
    ///
    /// The time complexity is O(n).
    pub fn len(&self) -> usize {
        // Usually, second is empty.
        self.first.len() + self.second.len() - self.second.intersection(self.first).count()
    }
}

/// Get the approximate size of entry
#[inline]
pub fn entry_approximate_size(e: &Entry) -> usize {
    //  message Entry {
    //      EntryType entry_type = 1;
    //      uint64 term = 2;
    //      uint64 index = 3;
    //      bytes data = 4;
    //      bytes context = 6;
    //      bool sync_log = 5;(Deprecated)
    // }
    // Each field has tag(1 byte) if it's not default value.
    // Tips: x bytes can represent a value up to 1 << x*7 - 1,
    // So 1 byte => 127, 2 bytes => 16383, 3 bytes => 2097151.
    // If entry_type is normal(default), in general, the size should
    // be tag(4) + term(1) + index(2) + data(2) + context(1) = 10.
    // If entry_type is conf change, in general, the size should be
    // tag(5) + entry_type(1) + term(1) + index(2) + data(1) + context(1) = 11.
    // We choose 12 in case of large index or large data for normal entry.
    e.data.len() + e.context.len() + 12
}

// Task 8 Route B — limit_size correspondence test
// Mirrors formal-verification/tests/limit_size/cases.json
// and FVSquad/LimitSizeCorrespondence.lean exactly.
#[cfg(test)]
mod tests {
    use super::*;
    use crate::eraftpb::Entry;

    /// Build an Entry whose compute_size() equals `size`.
    /// For data-only encoding: tag(1) + varint_len(n_bytes) + n_bytes.
    /// size=100 → data=98 bytes (tag=1, varint=1, data=98).
    /// size=200 → data=197 bytes (tag=1, varint=2, data=197).
    fn entry_of_size(size: usize) -> Entry {
        let mut e = Entry::default();
        let data_len = match size {
            100 => 98,
            200 => 197,
            _ => {
                // For sizes where data_len < 128: data_len = size - 2
                // For sizes where data_len >= 128: data_len = size - 3
                if size < 130 { size - 2 } else { size - 3 }
            }
        };
        e.data = vec![0u8; data_len].into();
        e
    }

    #[test]
    fn test_limit_size_correspondence() {
        // (sizes, budget_opt, expected_len)
        // Mirrors formal-verification/tests/limit_size/cases.json exactly.
        let cases: &[(&[usize], Option<u64>, usize)] = &[
            // Case 1: empty list unchanged
            (&[], Some(100), 0),
            // Case 2: singleton always kept (even budget=0)
            (&[100], Some(0), 1),
            // Case 3: all 5 fit at budget=500 (cumulative: first kept, then 200≤500...500≤500)
            (&[100, 100, 100, 100, 100], Some(500), 5),
            // Case 4: 4 kept (5th: cum=500>400)
            (&[100, 100, 100, 100, 100], Some(400), 4),
            // Case 5: 2 kept (3rd: cum=300>220)
            (&[100, 100, 100, 100, 100], Some(220), 2),
            // Case 6: 1 kept (2nd: cum=200>100)
            (&[100, 100, 100, 100, 100], Some(100), 1),
            // Case 7: 1 kept (budget=0: first always, 2nd: 100>0 → stop)
            (&[100, 100, 100, 100, 100], Some(0), 1),
            // Case 8: mixed [200,100,100], budget=350 → 2 kept (3rd: 400>350)
            (&[200, 100, 100], Some(350), 2),
            // Case 9: mixed [200,100,100], budget=200 → 1 kept (2nd: 300>200)
            (&[200, 100, 100], Some(200), 1),
            // Case 10: no limit → all kept
            (&[100, 100, 100], None, 3),
        ];

        for (i, &(sizes, budget, expected_len)) in cases.iter().enumerate() {
            let mut entries: Vec<Entry> = sizes.iter().map(|&s| entry_of_size(s)).collect();
            // Verify our size helper matches compute_size()
            for (j, (e, &s)) in entries.iter().zip(sizes.iter()).enumerate() {
                let actual_size = e.compute_size() as usize;
                assert_eq!(
                    actual_size, s,
                    "case {}: entry {} has compute_size()={} but expected {}",
                    i + 1, j, actual_size, s
                );
            }
            limit_size(&mut entries, budget);
            assert_eq!(
                entries.len(),
                expected_len,
                "case {}: limit_size(sizes={sizes:?}, budget={budget:?}) = len {}, want {expected_len}",
                i + 1,
                entries.len()
            );
        }
    }
}
