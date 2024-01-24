
some abstract sig Player{}
one abstract sig Demon extends Player {}
some abstract sig Minion extends Player {}
some abstract sig Outsider extends Player {}
some abstract sig Townsfolk extends Player {}

some abstract sig StartingInfo extends Townsfolk {}
some abstract sig OngoingInfo extends Townsfolk {}
some abstract sig Protection extends Townsfolk {}
some abstract sig Abilities extends Townsfolk {}

lone sig Washerwoman extends StartingInfo {}
lone sig Librarian extends StartingInfo {}
lone sig Investigator extends StartingInfo {}
lone sig Chef extends StartingInfo {}
lone sig Empath extends OngoingInfo {}
lone sig FortuneTeller extends OngoingInfo {}
lone sig Undertaker extends OngoingInfo {}
lone sig Monk extends Protection {}
lone sig Soldier extends Protection {}
lone sig Mayor extends Protection {}
lone sig RavenKeeper extends Abilities {}
lone sig Virgin extends Abilities {}
lone sig Slayer extends Abilities {}
lone sig Butler extends Outsider {}
lone sig Drunk extends Outsider {}
lone sig Recluse extends Outsider {}
lone sig Saint extends Outsider {}
lone sig Poisoner extends Minion {}
lone sig Spy extends Minion {}
lone sig ScarletWoman extends Minion {}
lone sig Baron extends Minion {}
lone sig Imp extends Demon {}

run show {

	#Player > 7

} for 13 Player
