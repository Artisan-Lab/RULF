use crate::clean;
use crate::docfs::PathError;
use crate::error::Error;
use crate::html::format::Buffer;
use crate::html::highlight;
use crate::html::layout;
use crate::html::render::{Context, BASIC_KEYWORDS};
use crate::visit::DocVisitor;

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_middle::ty::TyCtxt;
use rustc_session::Session;
use rustc_span::source_map::FileName;

use std::ffi::OsStr;
use std::fs;
use std::path::{Component, Path, PathBuf};
use std::rc::Rc;

pub(crate) fn render(cx: &mut Context<'_>, krate: &clean::Crate) -> Result<(), Error> {
    info!("emitting source files");

    let dst = cx.dst.join("src").join(krate.name(cx.tcx()).as_str());
    cx.shared.ensure_dir(&dst)?;

    let mut collector = SourceCollector { dst, cx, emitted_local_sources: FxHashSet::default() };
    collector.visit_crate(krate);
    Ok(())
}

pub(crate) fn collect_local_sources<'tcx>(
    tcx: TyCtxt<'tcx>,
    src_root: &Path,
    krate: &clean::Crate,
) -> FxHashMap<PathBuf, String> {
    let mut lsc = LocalSourcesCollector { tcx, local_sources: FxHashMap::default(), src_root };
    lsc.visit_crate(krate);
    lsc.local_sources
}

struct LocalSourcesCollector<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    local_sources: FxHashMap<PathBuf, String>,
    src_root: &'a Path,
}

fn is_real_and_local(span: clean::Span, sess: &Session) -> bool {
    span.cnum(sess) == LOCAL_CRATE && span.filename(sess).is_real()
}

impl LocalSourcesCollector<'_, '_> {
    fn add_local_source(&mut self, item: &clean::Item) {
        let sess = self.tcx.sess;
        let span = item.span(self.tcx);
        let Some(span) = span else { return };
        // skip all synthetic "files"
        if !is_real_and_local(span, sess) {
            return;
        }
        let filename = span.filename(sess);
        let p = if let FileName::Real(file) = filename {
            match file.into_local_path() {
                Some(p) => p,
                None => return,
            }
        } else {
            return;
        };
        if self.local_sources.contains_key(&*p) {
            // We've already emitted this source
            return;
        }

        let mut href = String::new();
        clean_path(self.src_root, &p, false, |component| {
            href.push_str(&component.to_string_lossy());
            href.push('/');
        });

        let mut src_fname = p.file_name().expect("source has no filename").to_os_string();
        src_fname.push(".html");
        href.push_str(&src_fname.to_string_lossy());
        self.local_sources.insert(p, href);
    }
}

impl DocVisitor for LocalSourcesCollector<'_, '_> {
    fn visit_item(&mut self, item: &clean::Item) {
        self.add_local_source(item);

        self.visit_item_recur(item)
    }
}

/// Helper struct to render all source code to HTML pages
struct SourceCollector<'a, 'tcx> {
    cx: &'a mut Context<'tcx>,

    /// Root destination to place all HTML output into
    dst: PathBuf,
    emitted_local_sources: FxHashSet<PathBuf>,
}

impl DocVisitor for SourceCollector<'_, '_> {
    fn visit_item(&mut self, item: &clean::Item) {
        if !self.cx.include_sources {
            return;
        }

        let tcx = self.cx.tcx();
        let span = item.span(tcx);
        let Some(span) = span else { return };
        let sess = tcx.sess;

        // If we're not rendering sources, there's nothing to do.
        // If we're including source files, and we haven't seen this file yet,
        // then we need to render it out to the filesystem.
        if is_real_and_local(span, sess) {
            let filename = span.filename(sess);
            let span = span.inner();
            let pos = sess.source_map().lookup_source_file(span.lo());
            let file_span = span.with_lo(pos.start_pos).with_hi(pos.end_pos);
            // If it turns out that we couldn't read this file, then we probably
            // can't read any of the files (generating html output from json or
            // something like that), so just don't include sources for the
            // entire crate. The other option is maintaining this mapping on a
            // per-file basis, but that's probably not worth it...
            self.cx.include_sources = match self.emit_source(&filename, file_span) {
                Ok(()) => true,
                Err(e) => {
                    self.cx.shared.tcx.sess.span_err(
                        span,
                        &format!(
                            "failed to render source code for `{}`: {}",
                            filename.prefer_local(),
                            e,
                        ),
                    );
                    false
                }
            };
        }

        self.visit_item_recur(item)
    }
}

impl SourceCollector<'_, '_> {
    /// Renders the given filename into its corresponding HTML source file.
    fn emit_source(
        &mut self,
        filename: &FileName,
        file_span: rustc_span::Span,
    ) -> Result<(), Error> {
        let p = match *filename {
            FileName::Real(ref file) => {
                if let Some(local_path) = file.local_path() {
                    local_path.to_path_buf()
                } else {
                    unreachable!("only the current crate should have sources emitted");
                }
            }
            _ => return Ok(()),
        };
        if self.emitted_local_sources.contains(&*p) {
            // We've already emitted this source
            return Ok(());
        }

        let contents = match fs::read_to_string(&p) {
            Ok(contents) => contents,
            Err(e) => {
                return Err(Error::new(e, &p));
            }
        };

        // Remove the utf-8 BOM if any
        let contents = contents.strip_prefix('\u{feff}').unwrap_or(&contents);

        let shared = Rc::clone(&self.cx.shared);
        // Create the intermediate directories
        let mut cur = self.dst.clone();
        let mut root_path = String::from("../../");
        clean_path(&shared.src_root, &p, false, |component| {
            cur.push(component);
            root_path.push_str("../");
        });

        shared.ensure_dir(&cur)?;

        let src_fname = p.file_name().expect("source has no filename").to_os_string();
        let mut fname = src_fname.clone();
        fname.push(".html");
        cur.push(&fname);

        let title = format!("{} - source", src_fname.to_string_lossy());
        let desc = format!("Source of the Rust file `{}`.", filename.prefer_remapped());
        let page = layout::Page {
            title: &title,
            css_class: "source",
            root_path: &root_path,
            static_root_path: shared.static_root_path.as_deref(),
            description: &desc,
            keywords: BASIC_KEYWORDS,
            resource_suffix: &shared.resource_suffix,
        };
        let v = layout::render(
            &shared.layout,
            &page,
            "",
            |buf: &mut _| {
                let cx = &mut self.cx;
                print_src(
                    buf,
                    contents,
                    file_span,
                    cx,
                    &root_path,
                    highlight::DecorationInfo::default(),
                    SourceContext::Standalone,
                )
            },
            &shared.style_files,
        );
        shared.fs.write(cur, v)?;
        self.emitted_local_sources.insert(p);
        Ok(())
    }
}

/// Takes a path to a source file and cleans the path to it. This canonicalizes
/// things like ".." to components which preserve the "top down" hierarchy of a
/// static HTML tree. Each component in the cleaned path will be passed as an
/// argument to `f`. The very last component of the path (ie the file name) will
/// be passed to `f` if `keep_filename` is true, and ignored otherwise.
pub(crate) fn clean_path<F>(src_root: &Path, p: &Path, keep_filename: bool, mut f: F)
where
    F: FnMut(&OsStr),
{
    // make it relative, if possible
    let p = p.strip_prefix(src_root).unwrap_or(p);

    let mut iter = p.components().peekable();

    while let Some(c) = iter.next() {
        if !keep_filename && iter.peek().is_none() {
            break;
        }

        match c {
            Component::ParentDir => f("up".as_ref()),
            Component::Normal(c) => f(c),
            _ => continue,
        }
    }
}

pub(crate) enum SourceContext {
    Standalone,
    Embedded { offset: usize },
}

/// Wrapper struct to render the source code of a file. This will do things like
/// adding line numbers to the left-hand side.
pub(crate) fn print_src(
    buf: &mut Buffer,
    s: &str,
    file_span: rustc_span::Span,
    context: &Context<'_>,
    root_path: &str,
    decoration_info: highlight::DecorationInfo,
    source_context: SourceContext,
) {
    let lines = s.lines().count();
    let mut line_numbers = Buffer::empty_from(buf);
    line_numbers.write_str("<pre class=\"src-line-numbers\">");
    match source_context {
        SourceContext::Standalone => {
            for line in 1..=lines {
                writeln!(line_numbers, "<span id=\"{0}\">{0}</span>", line)
            }
        }
        SourceContext::Embedded { offset } => {
            for line in 1..=lines {
                writeln!(line_numbers, "<span>{0}</span>", line + offset)
            }
        }
    }
    line_numbers.write_str("</pre>");
    let current_href = &context
        .href_from_span(clean::Span::new(file_span), false)
        .expect("only local crates should have sources emitted");
    highlight::render_source_with_highlighting(
        s,
        buf,
        line_numbers,
        highlight::HrefContext { context, file_span, root_path, current_href },
        decoration_info,
    );
}
