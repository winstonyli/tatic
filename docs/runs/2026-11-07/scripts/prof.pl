# prof.pl <dir> <exe> <libmatch>: self and inclusive busy-sample shares by function of <dir>/wf.json.gz (samply, presymbolicated),
# naming exe frames with llvm-symbolizer (inlined frames expanded, image base 0x140000000). Perl port of prof_named.py.
use strict; use warnings; use JSON::PP; use IO::Uncompress::Gunzip qw(gunzip $GunzipError);
my ($D, $EXE, $LIB) = @ARGV;
my $raw; gunzip("$D/wf.json.gz" => \$raw) or die $GunzipError;
my $p = decode_json($raw);
my @libs = @{$p->{libs}};
my @threads = (@{$p->{threads} || []}, map { @{$_->{threads}} } @{$p->{processes} || []});
my $IDLE = qr/^(NtWaitFor|NtDelayExecution|NtWaitForWorkViaWorkerFactory|ZwWaitFor|NtRemoveIoCompletion|NtWaitForAlertByThreadId)/;
my @samples; my %addrs;
for my $t (@threads) {
  my ($S, $ft, $fu, $st, $rt) = @$t{qw(stringArray frameTable funcTable stackTable resourceTable)};
  my %cache;
  my $frame = sub { my $fr = shift; return $cache{$fr} if exists $cache{$fr};
    my $f = $ft->{func}[$fr]; my $res = $fu->{resource}[$f];
    my $lib = (defined $res && $res >= 0 && $rt) ? $libs[$rt->{lib}[$res]]{debugName} : '';
    my $n = $S->[$fu->{name}[$f]];
    my $out;
    if ($lib =~ /$LIB/i) { my $a = $ft->{address} ? $ft->{address}[$fr] : undef;
      if (!defined $a || $a < 0) { $a = $n =~ /^(?:fun_|0x)([0-9a-f]+)$/ ? hex $1 : undef }
      $out = ['exe', $a]; $addrs{$a} = 1 if defined $a }
    else { $out = ['name', "$lib!$n"] }
    $cache{$fr} = $out };
  for my $s (@{$t->{samples}{stack}}) { next unless defined $s; my @c;
    while (defined $s) { push @c, $frame->($st->{frame}[$s]); $s = $st->{prefix}[$s] }
    next if $c[0][0] eq 'name' && $c[0][1] =~ /!$IDLE/;
    push @samples, \@c }
}
my @al = sort { $a <=> $b } keys %addrs;
my $in = "$D/addrs.txt"; open my $h, '>', $in or die; printf $h "0x%x\n", 0x140000000 + $_ for @al; close $h;
my $out = `llvm-symbolizer --obj="$EXE" --functions=linkage --demangle --inlining < "$in"`;
$out =~ s/\r//g; my @blocks = split /\n\n/, $out =~ s/\n+\z//r;
die "blocks ".@blocks." vs ".@al if @blocks != @al;
sub short { my $s = shift; 1 while $s =~ s/<[^<>]*>//g; $s =~ s/::h[0-9a-f]{16}$//; $s =~ s/\{\{closure\}\}/{closure}/g; $s }
my %names; # addr -> [innermost..outermost]
for my $i (0..$#al) { my @l = split /\n/, $blocks[$i]; my @n; for (my $j = 0; $j < @l; $j += 2) { push @n, short($l[$j]) } $names{$al[$i]} = \@n }
my (%self, %incl); my $N = @samples;
for my $c (@samples) { my @flat = map { $_->[0] eq 'exe' ? @{$names{$_->[1]} // ['?']} : ($_->[1]) } @$c;
  $self{$flat[0]}++; my %seen; $incl{$_}++ for grep { !$seen{$_}++ } @flat }
print "busy samples $N\n-- self --\n";
printf "%5.1f%% %s\n", 100 * $self{$_} / $N, $_ for (sort { $self{$b} <=> $self{$a} } keys %self)[0..24];
print "-- inclusive (church_bv / tatic) --\n";
printf "%5.1f%% %s\n", 100 * $incl{$_} / $N, $_ for (grep { /church_bv|tatic/ } sort { $incl{$b} <=> $incl{$a} } keys %incl)[0..44];
