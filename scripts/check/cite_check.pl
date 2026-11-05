# cite_check.pl <repo root> [doc...]: section cites in the live docs resolve. A cite is `<long doc>`, "Title" (also: section "Title",
# sections "A" and "B" is not parsed; one title per cite) where <long doc> is docs/tier-cycle/ or docs/related-work/ (one file per section). The target
# resolves when some line of it (any file under the directory), after stripping heading, list and emphasis markers, starts with the title (a title may stop at the
# line's first " (" or ":" part). Prints each unresolved cite as `<doc>: <target> "<title>"` and a count line; exit 1 if any.
# A `§N` next to docs/related-work/ (either order, `§9 and §12` too) resolves when that directory has a file N-*.md.
use strict; use warnings; use File::Find;
my $root = shift or die "usage: cite_check.pl <repo root> [doc...]\n";
chdir $root or die "$root: $!\n";
my @targets = qw(docs/tier-cycle/ docs/related-work/);
my %files; for my $d (@targets) { find(sub { push @{ $files{$d} }, $File::Find::name if -f && /.md$/ && $_ ne "README.md" }, $d) if -d $d }
my @docs = @ARGV ? @ARGV : (qw(README.md CLAUDE.md PARKED.md ROADMAP.md docs/TOUR.md docs/learned-vs-fixed.md docs/types.md docs/proven.md docs/syntax.md docs/benchmarks.md docs/design-notes.md docs/loop-experiment.md), map { sort @{ $files{$_} || [] } } @targets);
sub norm { my $s = shift; $s =~ s/\s+/ /g; $s =~ s/^ //; $s =~ s/ $//; $s }
my %anchors;
for my $f (@targets) {
  for my $src (sort @{ $files{$f} || [] }) {
    open my $fh, "<", $src or next;
    while (my $l = <$fh>) {
      chomp $l; $l =~ s/^\s*(?:#+\s*|[-*]\s+|\*+|_)+//; $l = norm($l);
      push @{ $anchors{$f} }, $l if length $l;
    }
  }
}
my ($n, $bad) = (0, 0);
my $alt = join '|', map { quotemeta } @targets;
for my $doc (@docs) {
  open my $fh, '<', $doc or next;
  local $/; my $t = <$fh>;
  while ($t =~ /($alt)`?,?\s+(?:sections?\s+)?["\x{201c}]([^"\x{201d}]{3,100})["\x{201d}]/g) {
    my ($f, $title) = ($1, norm($2)); $n++;
    (my $s = $title) =~ s/[.,;:]+$//;
    my $ok = grep { index($_, $s) == 0 } @{ $anchors{$f} || [] };
    unless ($ok) { $bad++; print "$doc: $f \"$title\"\n" }
  }
  my $rw = qr{docs/related-work/};
  my $list = qr{§\d+(?:(?:,\s+|\s+and\s+|\s+to\s+|-)§?\d+)*};
  while ($t =~ /(?:$rw`?,?\s+($list)|($list)\s+of\s+`?$rw)/g) {
    for my $s (($1 // $2) =~ /\d+/g) {
      $n++;
      next if grep { m{/0*$s-[^/]*$} } @{ $files{"docs/related-work/"} || [] };
      $bad++; print "$doc: docs/related-work/ §$s\n";
    }
  }
}
print "$n section cites checked, $bad unresolved\n";
exit($bad ? 1 : 0);
