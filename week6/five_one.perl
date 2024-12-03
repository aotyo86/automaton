use strict;
use warnings;
use Time::HiRes qw(gettimeofday tv_interval);

my $target = "aabaaababaaab"; # テスト対象の文字列
my $regex = '^(a|b)*a(a|b)$'; # 正規表現
my $start_time = [gettimeofday];

while ($target =~ m/$regex/g) {
    my $match = $&;         # マッチした部分文字列
    my $start = $-[0];      # マッチの開始位置
    my $end = $+[0] - 1;    # マッチの終了位置
    print "Pattern match succeeded\n";
    print "Match: $match\n";
    print "Start: $start, End: $end\n";
}

my $elapsed = tv_interval($start_time);
print "Execution Time: ${elapsed}s\n";
