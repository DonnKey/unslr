my $basics1 = "9 4
+ * ( ) a #
<E>

0   e   e  s2 e  s3 e    1
1   s4  s5 -  e  -  a
2   e   e  s2 e  s3 e    6
3   r4  r4 e  r4 e  r4
4   e   e  s2 e  s3 e    7
5   e   e  s2 e  s3 e    8
6   s4  s5 -  s9 -  e
";

my $basics3 = "9   r3  r3 e  r3 e  r3
";

my $gramFile = "build/test81gram";

for($i=0; $i<81; $i++) {
    my $i0 = $i % 3;
    my $i1 = ($i/3) % 3;
    my $i2 = ($i/(3*3)) % 3;
    my $i3 = ($i/(3*3*3)) % 3;

    my $s0 = ("*s4", "*r1", "e  ")[$i0];
    my $s1 = ("*s5", "*r1", "e  ")[$i1];
    my $s2 = ("*s4", "*r2", "e  ")[$i2];
    my $s3 = ("*s5", "*r2", "e  ")[$i3];

    open(G, ">", $gramFile) or die $!;

    print "case $i  -----------------------------------------------------------------------\n";
    print G $basics1;
    print   "7   $s0 $s1 -  r1 -  r1\n";
    print G "7   $s0 $s1 -  r1 -  r1\n";
    print   "8   $s2 $s3 -  r2 -  r2\n";
    print G "8   $s2 $s3 -  r2 -  r2\n";
    print G $basics3;

    close(G);

    my $cmd = "build/unslr fg sd pt d1 <$gramFile";
    print("$cmd\n");
    system("$cmd");

    $cmd = "../cmptab/build/cmptab il sl fg pf ie <unslr.out\n";
    print("$cmd\n");
    system("$cmd");
}

