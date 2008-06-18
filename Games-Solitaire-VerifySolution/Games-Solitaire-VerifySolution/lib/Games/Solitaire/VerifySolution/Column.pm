package Games::Solitaire::VerifySolution::Column;

use warnings;
use strict;

=head1 NAME

Games::Solitaire::VerifySolution::Column - a class wrapper for Solitaire
columns that are composed of a sequence of cards.

=head1 VERSION

Version 0.01

=cut

our $VERSION = '0.01';

use base 'Games::Solitaire::VerifySolution::Base';

use Games::Solitaire::VerifySolution::Exception;
use Games::Solitaire::VerifySolution::Card;

__PACKAGE__->mk_accessors(qw(
    _cards
    ));

=head1 SYNOPSIS

    use Games::Solitaire::VerifySolution::Column;

    # Initialise a column
    my $column = Games::Solitaire::VerifySolution::Column->new(
        {
            string => ": KH QS 5C",
        },
    );

    # Prints 3
    print $column->len();

    my $queen_card = $column->pos(1);

=head1 FUNCTIONS

=cut

sub _card_num_normalize
{
    my $arg = shift;

    if (ref($arg) eq "")
    {
        return +{ map { $_ => $arg } (qw(t non_t)) };
    }
    else
    {
        return $arg
    }
}

my @card_nums =  (map { _card_num_normalize($_) } 
    ("A", (2 .. 9), 
    {
        't' => "T",
        'non_t' => "10",
    },
    , "J", "Q", "K"));

my %ranks_map = (map { $card_nums[$_]->{t} => ($_+1) } (0 .. $#card_nums));

my %suits_map =
(
    "H" => { name => "hearts",   color => "red", },
    "S" => { name => "spades",   color => "black", },
    "C" => { name => "clubs",    color => "black", },
    "D" => { name => "diamonds", color => "red", },
);

sub _from_string
{
    my ($self, $str) = @_;

    if ($str !~ s{\A: }{})
    {
        Games::Solitaire::VerifySolution::Exception::Parse::Column::Prefix->throw(
            error => "String does not start with \": \"",
        );
    }

    # Ignore trailing whitespace, so we don't have -1.
    my @cards = split(/ +/, $str);

    $self->_cards(
        [
            map
            { 
                Games::Solitaire::VerifySolution::Card->new(
                    {string => $_ } 
                )
            }
            @cards
        ]
    );

    return;
}

sub _init
{
    my ($self, $args) = @_;

    if (exists($args->{string}))
    {
        return $self->_from_string($args->{string});
    }
}

=head2 $column->len()

Returns an integer representing the number of cards in the column.

=cut

sub len
{
    my $self = shift;

    return scalar(@{$self->_cards()});
}

=head2 $column->pos($idx)

Returns the card (a L<Games::Solitaire::VerifySolution::Card> object)
at position $idx in Column. $idx starts at 0.

=cut

sub pos
{
    my $self = shift;
    my $idx = shift;

    return $self->_cards->[$idx];
}

=head2 $column->clone()

Returns a clone of the column.

=cut

=begin Nothing

sub clone
{
    my $self = shift;

    my $new_card = Games::Solitaire::VerifySolution::Card->new();

    $new_card->suit($self->suit());
    $new_card->rank($self->rank());

    return $new_card;
}

=end Nothing

=cut

=head1 AUTHOR

Shlomi Fish, C<< <shlomif at iglu.org.il> >>

=head1 BUGS

Please report any bugs or feature requests to C<bug-games-solitaire-verifysolution-move at rt.cpan.org>, or through
the web interface at L<http://rt.cpan.org/NoAuth/ReportBug.html?Queue=Games-Solitaire-VerifySolution>.  I will be notified, and then you'll
automatically be notified of progress on your bug as I make changes.

=head1 SUPPORT

You can find documentation for this module with the perldoc command.

    perldoc Games::Solitaire::VerifySolution::Column


You can also look for information at:

=over 4

=item * RT: CPAN's request tracker

L<http://rt.cpan.org/NoAuth/Bugs.html?Dist=Games-Solitaire-VerifySolution>

=item * AnnoCPAN: Annotated CPAN documentation

L<http://annocpan.org/dist/Games-Solitaire-VerifySolution>

=item * CPAN Ratings

L<http://cpanratings.perl.org/d/Games-Solitaire-VerifySolution>

=item * Search CPAN

L<http://search.cpan.org/dist/Games-Solitaire-VerifySolution>

=back


=head1 ACKNOWLEDGEMENTS


=head1 COPYRIGHT & LICENSE

Copyright 2008 Shlomi Fish, all rights reserved.

This program is released under the following license: MIT/X11
( L<http://www.opensource.org/licenses/mit-license.php> ).

=cut

1; # End of Games::Solitaire::VerifySolution::Move
