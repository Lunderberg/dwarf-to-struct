use std::path::PathBuf;

use clap::Parser as _;
use itertools::Itertools as _;

use fallible_iterator::FallibleIterator;
use gimli::{DebuggingInformationEntry, Dwarf, Reader, Unit, UnitOffset, UnitRef};
use object::{Object, ObjectSection};

mod errors;
use errors::Error;

mod relocation_map;
use relocation_map::*;

#[derive(clap::Parser)]
struct CommandLineInterface {
    #[arg(long, value_name = "SHARED_OBJECT")]
    shared_object_path: Option<PathBuf>,

    #[arg(long = "name")]
    class_name: Option<String>,

    #[arg(long = "base-class")]
    base_class_name: Option<String>,

    #[arg(long = "contains")]
    contained_class_name: Option<String>,
}

struct SearchFilter {
    class_name: Option<String>,
    base_class_name: Option<String>,
    contained_class_name: Option<String>,
}

struct EntryChildrenIterator<'a, 'b, R: Reader> {
    cursor: gimli::EntriesCursor<'a, 'b, R>,
    is_first: bool,
}

impl<'a, 'b, R: Reader> EntryChildrenIterator<'a, 'b, R> {
    fn new(cursor: gimli::EntriesCursor<'a, 'b, R>) -> Self {
        Self {
            cursor,
            is_first: true,
        }
    }
}

impl<'a, 'b, R: Reader> Iterator for EntryChildrenIterator<'a, 'b, R> {
    type Item = gimli::DebuggingInformationEntry<'a, 'b, R>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.is_first {
            self.is_first = false;
            self.cursor
                .next_dfs()
                .unwrap()
                .filter(|(delta_depth, _)| *delta_depth == 1)
                .map(|(_, entry)| entry.clone())
        } else {
            self.cursor.next_sibling().unwrap().cloned()
        }
    }
}

trait UnitExt<R: Reader> {
    fn iter_root<'a>(&'a self) -> impl Iterator<Item = DebuggingInformationEntry<'a, 'a, R>> + 'a
    where
        R: 'a,
        R::Offset: 'a;

    fn iter_children<'a>(
        &'a self,
        offset: UnitOffset<R::Offset>,
    ) -> impl Iterator<Item = DebuggingInformationEntry<'a, 'a, R>> + 'a
    where
        R: 'a,
        R::Offset: 'a;
}
impl<R: Reader> UnitExt<R> for Unit<R> {
    fn iter_root<'a>(&'a self) -> impl Iterator<Item = DebuggingInformationEntry<'a, 'a, R>> + 'a
    where
        R: 'a,
        R::Offset: 'a,
    {
        let mut cursor = self.entries();
        assert!(cursor.next_dfs().unwrap().is_some());
        EntryChildrenIterator::new(cursor)
    }

    fn iter_children<'a>(
        &'a self,
        offset: UnitOffset<R::Offset>,
    ) -> impl Iterator<Item = DebuggingInformationEntry<'a, 'a, R>> + 'a
    where
        R: 'a,
        R::Offset: 'a,
    {
        let mut cursor = self.entries_at_offset(offset).unwrap();
        assert!(cursor.next_dfs().unwrap().is_some());
        EntryChildrenIterator::new(cursor)
    }
}

trait EntryExt<R: Reader> {
    fn name(&self, unit: UnitRef<R>) -> Option<String>;

    fn size_bytes(&self) -> Option<usize>;

    fn member_location(&self) -> Option<usize>;

    fn class<'a>(&self, unit: UnitRef<'a, R>) -> Option<DebuggingInformationEntry<'a, 'a, R>>;

    fn iter_children<'a>(
        &self,
        unit: &'a Unit<R>,
    ) -> impl Iterator<Item = DebuggingInformationEntry<'a, 'a, R>> + 'a
    where
        R: 'a,
        R::Offset: 'a;

    fn iter_base_classes<'a>(
        &self,
        unit: UnitRef<'a, R>,
    ) -> impl Iterator<Item = DebuggingInformationEntry<'a, 'a, R>> + 'a
    where
        R: 'a,
        R::Offset: 'a,
    {
        self.iter_children(unit.unit)
            .filter(|child| child.tag() == gimli::DW_TAG_inheritance)
            .filter_map(move |child| child.class(unit))
    }

    fn iter_member_classes<'a>(
        &self,
        unit: UnitRef<'a, R>,
    ) -> impl Iterator<Item = DebuggingInformationEntry<'a, 'a, R>> + 'a
    where
        R: 'a,
        R::Offset: 'a,
    {
        self.iter_children(unit.unit)
            .filter(|child| child.tag() == gimli::DW_TAG_member)
            .filter(|child| child.member_location().is_some())
            .filter_map(move |child| child.class(unit))
    }
}

impl<'a, 'b, R: Reader> EntryExt<R> for DebuggingInformationEntry<'a, 'b, R> {
    fn name(&self, unit: UnitRef<R>) -> Option<String> {
        self.attr_value(gimli::DW_AT_name)
            .unwrap()
            .map(|attr_value| {
                unit.attr_string(attr_value)
                    .unwrap()
                    .to_string_lossy()
                    .unwrap()
                    .into()
            })
    }

    fn size_bytes(&self) -> Option<usize> {
        self.attr_value(gimli::DW_AT_byte_size)
            .unwrap()
            .map(|attr_value| match attr_value {
                gimli::AttributeValue::Udata(data) => data as usize,
                _ => panic!("Invalid AttributeValue for byte size"),
            })
    }

    fn member_location(&self) -> Option<usize> {
        self.attr_value(gimli::DW_AT_data_member_location)
            .unwrap()
            .map(|attr_value| match attr_value {
                gimli::AttributeValue::Udata(data) => data as usize,
                _ => panic!("Invalid AttributeValue for member location"),
            })
    }

    fn class<'c>(&self, unit: UnitRef<'c, R>) -> Option<DebuggingInformationEntry<'c, 'c, R>> {
        self.attr_value(gimli::DW_AT_type)
            .unwrap()
            .map(|attr_value| match attr_value {
                gimli::AttributeValue::UnitRef(offset) => {
                    // This is the same as
                    // `unit.entry(offset).unwrap()`, but isn't
                    // restricted to the the lifetime of the temporary
                    // view produced by Deref.
                    unit.unit.entry(offset).unwrap()
                }

                gimli::AttributeValue::DebugInfoRef(offset) => {
                    todo!(
                        "Need to expose other compilation units \
                         for cross-CU reference {offset:?}"
                    )
                    // offset.to_debug_info_offset(&unit.unit.header).unwrap()
                }

                other => panic!(
                    "Invalid AttributeValue for type, \
                     must be reference into debug info section, \
                     but instead was {other:?}."
                ),
            })
    }

    fn iter_children<'c>(
        &self,
        unit: &'c Unit<R>,
    ) -> impl Iterator<Item = DebuggingInformationEntry<'c, 'c, R>> + 'c
    where
        R: 'c,
        R::Offset: 'c,
    {
        unit.iter_children(self.offset())
    }
}

fn dump_file<R: Reader>(dwarf: &Dwarf<R>, search_filter: &SearchFilter) -> Result<(), Error> {
    let units: Vec<_> = dwarf.units().map(|header| dwarf.unit(header)).collect()?;

    units.iter().for_each(|unit| {
        let unit = unit.unit_ref(&dwarf);

        unit.iter_root()
            .filter(|entry| entry.tag() == gimli::DW_TAG_class_type)
            .filter(|entry| entry.attr_value(gimli::DW_AT_byte_size).unwrap().is_some())
            .filter(|entry| {
                if let Some(required_class_name) = search_filter.class_name.as_ref() {
                    entry
                        .name(unit)
                        .map(|name| &name == required_class_name)
                        .unwrap_or(false)
                } else {
                    true
                }
            })
            .filter(|entry| {
                if let Some(required_base_class) = search_filter.base_class_name.as_ref() {
                    entry.iter_base_classes(unit).any(|base_class| {
                        base_class.name(unit).as_ref() == Some(required_base_class)
                    })
                } else {
                    true
                }
            })
            .filter(|entry| {
                if let Some(required_member_class) = search_filter.contained_class_name.as_ref() {
                    entry.iter_member_classes(unit).any(|base_class| {
                        base_class.name(unit).as_ref() == Some(required_member_class)
                    })
                } else {
                    true
                }
            })
            .unique_by(|entry| entry.name(unit))
            .enumerate()
            .for_each(|(i, entry)| {
                if i > 0 {
                    println!("");
                }

                let name = entry.name(unit).unwrap();
                let size_bytes = entry.size_bytes().unwrap();

                println!("struct {name} {{ // {size_bytes} bytes");

                entry
                    .iter_children(&unit)
                    .filter(|child| {
                        child.tag() == gimli::DW_TAG_member
                            || child.tag() == gimli::DW_TAG_inheritance
                    })
                    .filter(|child| child.member_location().is_some())
                    .for_each(|child| {
                        let class = child.class(unit).unwrap();
                        let class_name = class.name(unit).unwrap_or_else(|| "unknown_class".into());

                        let name = child.name(unit).unwrap_or_else(|| "unknown_name".into());

                        let field_size = class.size_bytes().unwrap_or(0);

                        let field_start = child.member_location().unwrap();
                        let field_end = field_start + field_size;

                        println!(
                            "    {class_name} {name}; \
                                     // {field_size} bytes, \
                                     {field_start}-{field_end}"
                        );
                    });

                println!("}};");
            });
    });

    Ok(())
}

fn main() -> Result<(), Error> {
    let cli_args = CommandLineInterface::parse();

    let shared_obj_path = if let Some(path) = cli_args.shared_object_path {
        path
    } else {
        let home_dir = std::env::var("HOME").map_err(|_| Error::NoHomeDirectoryFound)?;
        let mut path: std::path::PathBuf = home_dir.into();
        path.push(".steam");
        path.push("steam");
        path.push("steamapps");
        path.push("common");
        path.push("Stardew Valley");
        path.push("libcoreclr.so");
        path
    };

    let search_filter = SearchFilter {
        class_name: cli_args.class_name,
        base_class_name: cli_args.base_class_name,
        contained_class_name: cli_args.contained_class_name,
    };

    let shared_obj_bytes = std::fs::read(&shared_obj_path)?;
    let object = object::File::parse(&*shared_obj_bytes)?;
    let endian = if object.is_little_endian() {
        gimli::RunTimeEndian::Little
    } else {
        gimli::RunTimeEndian::Big
    };

    let debug_bytes = object
        .gnu_debuglink()?
        .map(|(name, _crc)| {
            let name = std::str::from_utf8(name).unwrap();
            let relative_path = std::path::Path::new(name);
            let full_path = shared_obj_path.with_file_name(relative_path);

            full_path
        })
        .filter(|path| std::path::Path::exists(path))
        .map(|path| std::fs::read(path).unwrap());

    let debug_obj = debug_bytes.as_ref().map(|bytes| {
        let dbg_obj = object::File::parse(bytes.as_slice()).unwrap();
        assert_eq!(object.is_little_endian(), dbg_obj.is_little_endian());
        dbg_obj
    });

    let dwarf_sections = gimli::DwarfSections::load(|id| -> Result<_, Error> {
        let name = id.name();
        let data = object
            .section_by_name(name)
            .or_else(|| {
                debug_obj
                    .as_ref()
                    .map(|obj| obj.section_by_name(name))
                    .flatten()
            })
            .map(|section| -> Result<_, Error> {
                Ok((
                    section.uncompressed_data()?,
                    RelocationMap(section.relocation_map()?),
                ))
            })
            .transpose()?
            .unwrap_or_else(Default::default);
        Ok(data)
    })?;

    let dwarf = dwarf_sections.borrow(|section: &(_, _)| {
        let slice = gimli::EndianSlice::new(std::borrow::Cow::as_ref(&section.0), endian);
        gimli::RelocateReader::new(slice, &section.1)
    });

    dump_file(&dwarf, &search_filter)?;

    Ok(())
}
