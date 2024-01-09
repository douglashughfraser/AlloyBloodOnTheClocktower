enum Status {
	Sober,
	IsDrunk,
	IsPoisoned,
	NotInPlay
}

some abstract sig Player{
	status: one Status
}{

}

abstract sig Townsfolk extends Player {}
abstract sig Outsider extends Player {}
abstract sig Minion extends Player {}
abstract sig Demon extends Player {
	bluffs: some Townsfolk + Outsider
}{
	#bluffs = 3

	// Bluffs aren't in the game
	one TS: TownSquare | no bluffs & TS.inGame
}

one sig TownSquare {
	inGame: set Player,
	drunkPlayer: lone Player,		// Up to one player can be drunk
	poisonedPlayer: lone Player 		// Up to one player can be poisoned
}{
	all player: Player | player in inGame iff not player.status = NotInPlay

	all player: Player | player in drunkPlayer iff player.status = IsDrunk
	all player: Player {
		player in poisonedPlayer iff player.status = IsPoisoned 
		player in poisonedPlayer iff {
			// Poisoner must be in the game and have chosen them (on the first night)
			one poisoner: Poisoner | poisoner in inGame and poisoner.poisoned = player
		}
	}

	// If a character is drunk then no drunk token is handed out
	#drunkPlayer > 0 implies not Drunk in inGame
}

fact setup {

	one TS: TownSquare {
		#TS.inGame >= 5

		// A demon is in the game
		one demon: Demon | demon in TS.inGame

		#Baron = 0 implies {
			#TS.inGame = 5 implies {	#(Townsfolk & TS.inGame) = 3
								#(Outsider & TS.inGame) = 0
								#(Minion & TS.inGame) = 1
			}
			#TS.inGame = 6 implies {	#(Townsfolk & TS.inGame) = 3
								#(Outsider & TS.inGame) = 1
								#(Minion & TS.inGame) = 1
			}
			#TS.inGame = 7 implies {	#(Townsfolk & TS.inGame) = 5
								#(Outsider & TS.inGame) = 0
								#(Minion & TS.inGame) = 1
			}
			#TS.inGame = 8 implies {	#(Townsfolk & TS.inGame) = 5
								#(Outsider & TS.inGame) = 1
								#(Minion & TS.inGame) = 1
			}
			#TS.inGame = 9 implies {	#(Townsfolk & TS.inGame) = 5
								#(Outsider & TS.inGame) = 2
								#(Minion & TS.inGame) = 1
			}
			#TS.inGame = 10 implies {	#(Townsfolk & TS.inGame) = 7
								#(Outsider & TS.inGame) = 0
								#(Minion & TS.inGame) = 2
			}
			#TS.inGame = 11 implies {	#(Townsfolk & TS.inGame) = 7
								#(Outsider & TS.inGame) = 1
								#(Minion & TS.inGame) = 2
			}
			#TS.inGame = 12 implies {	#(Townsfolk & TS.inGame) = 7
								#(Outsider & TS.inGame) = 2
								#(Minion & TS.inGame) = 2
			}
			#TS.inGame = 13 implies {	#(Townsfolk & TS.inGame) = 9
								#(Outsider & TS.inGame) = 0
								#(Minion & TS.inGame) = 3
			}
			#TS.inGame = 14 implies {	#(Townsfolk & TS.inGame) = 9
								#(Outsider & TS.inGame) = 1
								#(Minion & TS.inGame) = 3
			}
			#TS.inGame > 14 implies {	#(Townsfolk & TS.inGame) > 8
								#(Outsider & TS.inGame) > 2
								#(Minion & TS.inGame) > 2
			}
		} else #Baron = 1 implies {
			#TS.inGame = 5 implies {	#(Outsider & TS.inGame) = 2
								#(Minion & TS.inGame) = 1
			}
			#TS.inGame = 6 implies {	#(Townsfolk & TS.inGame) = 1
								#(Outsider & TS.inGame) = 3
								#(Minion & TS.inGame) = 1
			}
			#TS.inGame = 7 implies {	#(Townsfolk & TS.inGame) = 3
								#(Outsider & TS.inGame) = 2
								#(Minion & TS.inGame) = 1
			}
			#TS.inGame = 8 implies {	#(Townsfolk & TS.inGame) = 3
								#(Outsider & TS.inGame) = 3
								#(Minion & TS.inGame) = 1
			}
			#TS.inGame = 9 implies {	#(Townsfolk & TS.inGame) = 3
								#(Outsider & TS.inGame) = 4
								#(Minion & TS.inGame) = 1
			}
			#TS.inGame = 10 implies {	#(Townsfolk & TS.inGame) = 5
								#(Outsider & TS.inGame) = 2
								#(Minion & TS.inGame) = 2
			}	
			#TS.inGame = 11 implies {	#(Townsfolk & TS.inGame) = 5
								#(Outsider & TS.inGame) = 3
								#(Minion & TS.inGame) = 2
			}
			#TS.inGame = 12 implies {	#(Townsfolk & TS.inGame) = 5
								#(Outsider & TS.inGame) = 4
								#(Minion & TS.inGame) = 2
			}
			#TS.inGame = 13 implies {	#(Townsfolk & TS.inGame) = 7
								#(Outsider & TS.inGame) = 2
								#(Minion & TS.inGame) = 3
			}
			#TS.inGame = 14 implies {	#(Townsfolk & TS.inGame) = 7
								#(Outsider & TS.inGame) = 3
								#(Minion & TS.inGame) = 3
			}
			#TS.inGame > 14 implies {	#(Townsfolk & TS.inGame) > 8
								#(Outsider & TS.inGame) = 4
								#(Minion & TS.inGame) > 2
			}
		}
	}
}

run show {


	one TS: TownSquare {
		#TS.inGame >= 10
		#(TS.drunkPlayer + TS.poisonedPlayer) > 0
	}

	one player: Player | player in Washerwoman and not player.status = NotInPlay
	one player: Player | player in Investigator and not player.status = NotInPlay and player.minion not in Baron
	one player: Player | player in Librarian and not player.status = NotInPlay

	some player: Washerwoman + Investigator + Librarian | player.status = IsDrunk

} for exactly 16 Player

lone sig Washerwoman extends Townsfolk {
	townsfolk: lone Townsfolk,
	correct: lone Player,
	wrong: lone Player
}{
	// Both shown players are playing the game
	one TS:TownSquare | correct + wrong in TS.inGame

	// Different players are shown
	no correct & wrong

	// Avoid the case where showing a correct wrong
	no wrong & townsfolk

	// The player is not shown themselves at any point
	this not in townsfolk + correct + wrong

	// If not drunk or poisoned then the correct ping is actually correct
	status = Sober implies {
		// Correct ping is actually correct
		correct in townsfolk + Spy
	}

	// If not in the game (i.e. being used as a bluff), don't assign pings
	status = NotInPlay implies {
		no townsfolk and no correct and no wrong
	} else {
		some townsfolk and some correct and some wrong
	}
}

lone sig Librarian extends Townsfolk {
	outsider: lone Outsider,
	correct: lone Player,
	wrong: lone Player
}{
	// Both shown players are playing the game
	one TS:TownSquare | correct + wrong in TS.inGame

	// Different players are shown
	no correct & wrong

	// Avoid the case where showing a correct wrong
	no wrong & outsider

	// The player is not shown themselves at any point
	this not in outsider + correct + wrong

	// If not drunk or poisoned then the correct ping is actually correct
	status = Sober implies {
		// Correct ping is actually correct
		correct in outsider + Spy
	}

	// If not in the game (i.e. being used as a bluff), don't assign pings
	status = NotInPlay implies {
		no outsider and no correct and no wrong
	} else {
		some outsider and some correct and some wrong
	}
}

lone sig Investigator extends Townsfolk {
	minion: lone Minion,
	correct: lone Player,
	wrong: lone Player
}{
	// Both shown players are playing the game
	one TS:TownSquare | correct + wrong in TS.inGame

	// Different players are shown
	no correct & wrong

	// Avoid the case where showing a correct wrong
	no wrong & minion

	// The player is not shown themselves at any point
	this not in minion + correct + wrong

	// If not drunk or poisoned then the correct ping is actually correct
	status = Sober implies {
		// Shown character is actually in play and could actually show as that character
		correct in minion + Recluse
	}

	// If not in the game (i.e. being used as a bluff), don't assign pings
	status = NotInPlay implies {
		no minion and no correct and no wrong
	} else {
		some minion and some correct and some wrong
	}
}

lone sig Chef extends Townsfolk {}
lone sig Empath extends Townsfolk {}

lone sig FortuneTeller extends Townsfolk {
	redherring: lone Townsfolk + Outsider
}{
	one TS:TownSquare | redherring in TS.inGame

	// If not in the game (i.e. being used as a bluff), don't assign redherring
	status = NotInPlay implies no redherring else some redherring
}

lone sig Undertaker extends Townsfolk {}
lone sig Monk extends Townsfolk {}
lone sig RavenKeeper extends Townsfolk {}
lone sig Virgin extends Townsfolk {}
lone sig Slayer extends Townsfolk {}
lone sig Soldier extends Townsfolk {}
lone sig Mayor extends Townsfolk {}
lone sig Butler extends Outsider {}
lone sig Drunk extends Outsider {}
lone sig Recluse extends Outsider {}
lone sig Saint extends Outsider {}

lone sig Poisoner extends Minion {
	poisoned: lone Townsfolk + Outsider
}{
	// If not in the game (i.e. being used as a bluff), don't assign poisoned
	status = NotInPlay implies no poisoned else some poisoned
}

lone sig Spy extends Minion {}
lone sig ScarletWoman extends Minion {}
lone sig Baron extends Minion {}
lone sig Imp extends Demon {}

