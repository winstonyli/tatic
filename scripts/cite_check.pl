# cite_check.pl <repo root> [doc...]: section cites in the live docs resolve. A cite is `<long doc>`, "Title" (also: section "Title",
# sections "A" and "B" is not parsed; one title per cite) where <long doc> is docs/tier-cycle.md or RELATED_WORK.md. The target
# resolves when some line of it, after stripping heading, list and emphasis markers, starts with the title (a title may stop at the
# line's first " (" or ":" part). Prints each unresolved cite as `<doc>: <target> "<title>"` and a count line; exit 1 if any.
use strict; use warnings;
my $root = shift or die "usage: cite_check.pl <repo root> [doc...]\n";
chdir $root or die "$root: $!\n";
my @targets = qw(docs/tier-cycle.md RELATED_WORK.md);
my @docs = @ARGV ? @ARGV : qw(README.md CLAUDE.md PARKED.md ROADMAP.md TYPES.md RELATED_WORK.md docs/TOUR.md docs/learned-vs-fixed.md docs/tier-cycle.md);
sub norm { my $s = shift; $s =~ s/\s+/ /g; $s =~ s/^ //; $s =~ s/ $//; $s }
my %anchors;
for my $f (@targets) {
  open my $fh, '<', $f or next;
  while (my $l = <$fh>) {
    chomp $l; $l =~ s/^\s*(?:#+\s*|[-*]\s+|\*+|_)+//; $l = norm($l);
    push @{ $anchors{$f} }, $l if length $l;
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
}
print "$n section cites checked, $bad unresolved\n";
exit($bad ? 1 : 0);
