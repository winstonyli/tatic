# path_cite_check.pl <repo root> [doc...]: every backticked repo path (`crates/...`, `scripts/...`, `tools/...`, `docs/...`,
# with any `#symbol` or `:line` suffix dropped) names a file or directory that exists, in every tracked .md, .rs, .sh and
# .toml file but the history (docs/superpowers/, docs/runs/, docs/runs.md) and the guards (scripts/check/). A cite on a line,
# or just after one, that says the thing is gone (deleted, removed, git show, recover, restore, revert, untracked,
# gitignored) is not checked: write "(deleted in <commit>)" beside a path you keep as history. No allowlist.
# Exit 1 naming each offender. path_cite_check_check.sh tests it.
use strict; use warnings;
my $root = shift @ARGV // '.';
chdir $root or die "no root $root\n";
my @docs = @ARGV ? @ARGV : split /\n/, `git ls-files "*.md" "*.rs" "*.sh" "*.toml" ":!docs/superpowers" ":!docs/runs" ":!docs/runs.md" ":!scripts/check"`;
my $gone = qr/deleted|removed|git show|recover|restore|revert|untracked|gitignored/i;
my ($n, $bad) = (0, 0);
for my $doc (@docs) {
  open my $fh, '<', $doc or next;
  my $prev = '';
  while (my $line = <$fh>) {
    while ($line =~ /`((?:crates|scripts|tools|docs)\/[^`\s]*)`/g) {
      my $p = $1;
      next if $p =~ /[*{}<>\$%|\\]/;      # globs, templates and placeholders name no one file
      $p =~ s/[#:].*$//; $p =~ s/[.,;)]+$//;
      next if $p eq '' || "$prev $line" =~ $gone;
      $n++;
      next if -e $p;
      print "$doc: `$p` does not exist (fix the path, or write \"(deleted in <commit>)\" beside it)\n"; $bad++;
    }
    $prev = $line;
  }
}
printf "%d path cites checked, %d broken\n", $n, $bad;
exit($bad ? 1 : 0);
