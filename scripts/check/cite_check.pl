# cite_check.pl <repo root> [doc...]: section cites resolve, in every tracked .md, .rs, .sh and .toml file but the history (docs/superpowers/, docs/runs/, docs/runs.md) and the guards (scripts/check/). A cite is `<long doc>`, "Title" (straight or curly quotes; also: section "Title",
# sections "A" and "B" is not parsed; one title per cite) where <long doc> is docs/tier-cycle/ or docs/related-work/ (one file per section). The target
# resolves when some line of it (any file under the directory), after stripping heading, list and emphasis markers, starts with the title, ending at a word boundary (a title may stop at the
# line's first " (" or ":" part). Prints each unresolved cite as `<doc>: <target> "<title>"` and a count line; exit 1 if any.
# A number next to docs/related-work/ (`§9`, `section 9`, `sec 9` or bare `9`; either order; `§9 and §12` too) resolves when that directory has a file N-*.md.
# Of a code file only the comments are read, without their markers, so a wrapped cite reads whole.
# Any other mention of either directory fails as "with no section": to point at a long doc as a whole, name its index, <long doc>README.md. A TOUR cite, <long doc>#Title, is tour_check.sh's. An old name of a long doc fails too.
use strict; use warnings; use utf8; use File::Find;
binmode STDOUT, ":encoding(UTF-8)";
my $root = shift or die "usage: cite_check.pl <repo root> [doc...]\n";
chdir $root or die "$root: $!\n";
my @targets = qw(docs/tier-cycle/ docs/related-work/);
my %files; for my $d (@targets) { find(sub { push @{ $files{$d} }, $File::Find::name if -f && /.md$/ && $_ ne "README.md" }, $d) if -d $d }
my @docs = @ARGV ? @ARGV : split /\n/, `git ls-files "*.md" "*.rs" "*.sh" "*.toml" ":!docs/superpowers" ":!docs/runs" ":!docs/runs.md" ":!scripts/check"`;
my %comment = (rs => qr{//[/!]?}, sh => qr{#}, toml => qr{#});
sub norm { my $s = shift; $s =~ s/\s+/ /g; $s =~ s/^ //; $s =~ s/ $//; $s }
my %anchors;
for my $f (@targets) {
  for my $src (sort @{ $files{$f} || [] }) {
    open my $fh, "<:encoding(UTF-8)", $src or next;
    while (my $l = <$fh>) {
      chomp $l; $l =~ s/^\s*(?:#+\s*|[-*]\s+|\*+|_)+//; $l = norm($l);
      push @{ $anchors{$f} }, $l if length $l;
    }
  }
}
my ($n, $bad) = (0, 0);
my $alt = join '|', map { quotemeta } @targets;
for my $doc (@docs) {
  open my $fh, '<:encoding(UTF-8)', $doc or next;
  local $/; my $t = <$fh>;
  my ($ext) = $doc =~ /\.(\w+)$/;
  if (my $c = $comment{$ext // ""}) { $t = join "", map { /$c(.*)/ ? "$1\n" : "" } split /^/, $t }
  while ($t =~ s/($alt)`?,?\s+\(?(?:sections?\s+)?["“]([^"”]{3,200})["”]//) {
    my ($f, $title) = ($1, norm($2)); $n++;
    (my $s = $title) =~ s/[.,;:]+$//;
    my $ok = grep { /^\Q$s\E(?!\w)/ } @{ $anchors{$f} || [] };
    unless ($ok) { $bad++; print "$doc: $f \"$title\"\n" }
  }
  my $rw = qr{docs/related-work/};
  my $sec = qr{(?:§|sections?\s+|sec\s+)};
  my $list = qr{$sec?\d+\b(?:(?:,\s+|\s+and\s+|\s+to\s+|-)$sec?\d+\b)*};
  while ($t =~ s/(?:$rw`?,?\s+($list)|($list)\s+of\s+`?$rw)//) {
    for my $s (($1 // $2) =~ /\d+/g) {
      $n++;
      next if grep { m{/0*$s-[^/]*$} } @{ $files{"docs/related-work/"} || [] };
      $bad++; print "$doc: docs/related-work/ §$s\n";
    }
  }
  while ($t =~ /(docs\/tier-cycle\.md|RELATED_WORK\.md|TYPES\.md)/g) { $bad++; print "$doc: $1 is an old name\n" }
  while ($t =~ /([^\n]{0,60})($alt)(?!README\.md|#)([^\n]{0,30})/g) { $bad++; print "$doc: $2 with no section: $1$2$3\n" }
}
print "$n section cites checked, $bad unresolved\n";
exit($bad ? 1 : 0);
