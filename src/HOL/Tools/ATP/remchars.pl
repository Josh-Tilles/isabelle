#!/usr/bin/perl
#
# isa2tex.pl - Converts isabelle formulae into LaTeX
# A complete hack - needs more work.
#
# by Michael Dales (michael@dcs.gla.ac.uk)

# Begin math mode
#printf "\$";
#ALL �xa�::�'a�::�type�.   (~ (�P�::�'a�::�type� => bool) (�x�::�'a�::�type�) | �P� �xa�) & (~ �P� �xa�# | �P� �x�)((�P�::�'a�::�type� => bool) (�xa�::�'a�::�type�) | (ALL �x�::�'a�::�type�. �P� �x�)) &((AL#L �x�::�'a�::�type�. ~ �P� �x�) | ~ �P� (�xb�::�'a�::�type�))
#perhaps change to all chars not in alphanumeric or a few symbols?

while (<STDIN>)
{

    #chop();
    s%\n$%%;
    s%�%%g;
    s%�%%g;
    s%�%%g;
    s%�%%g;
    s%�%%g;
    s%�%%g;
    
    #printf "$_\\newline\n";
    printf "$_";
}

# End math mode
#printf "\$\n";
#printf "\\end{tabbing}\n";
