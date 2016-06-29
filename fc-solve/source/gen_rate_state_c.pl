#!/usr/bin/perl

use strict;
use warnings;
use autodie;
use File::Spec;
use Path::Tiny;

my $src_dir = shift(@ARGV);

sub fn
{
    return File::Spec->catfile($src_dir, shift());
}

my $text = path(fn("rate_state.h"))->slurp_utf8;

my $type_name = 'fc_solve_seq_cards_power_type_t';
my $array_name = 'fc_solve_seqs_over_cards_lookup';
my $power_name = 'FCS_BEFS_SEQS_OVER_RENEGADE_CARDS_EXPONENT';
my ($power) = $text =~ m/^#define \Q$power_name\E (\d+\.\d+)\s*$/ms;
my ($decl, $limit) = $text =~ m/^extern\s+(const\s+\Q$type_name\E\s+\Q$array_name\E\[([^\]]+)\]);\s*$/ms;

if (!defined($power) or !defined($limit))
{
    die "Could not match power and/or limit";
}

my $top = eval($limit);

# my @data = (map { int( ($_ ** $power) * 128 * 1024 ) } (0 .. $top-1));
my @data = (map { $_ ** $power } (0 .. $top-1));

path(fn("rate_state.c"))->spew_utf8(<<"EOF");
/*
 * This file is part of Freecell Solver and was generated by
 * gen_rate_state_c.pl .
 * Do not modify directly.
 */

#include "rate_state.h"

/*
 * This contains the exponents of the first few integers to the power
 * of $power_name .
 */
$decl =
{
@{[join(", ", @data)]}
};
EOF
