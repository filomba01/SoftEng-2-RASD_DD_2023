-- Generalites such as name, surname 
sig Generalities{}
sig Email{}
sig Username{}
sig Password{}
sig TeamName{}


-- badges to be assign to a student
sig Badge{}
-- the rule of a badge
sig Rule{}


abstract sig User{
	generalities: one Generalities,
	email: one Email,
	

}

-- extends Users Participant
sig Student extends User {
	competitions: set Competition,
	badges: set Badge,
}

sig Educator extends User{
	creates_badges: set Badge,
	manage_competitions: set Competition,

}

sig Team extends Participant{
	students: set Student,
	name: one TeamName,
}

sig Participant{
	join_battle: set Battle
}

sig Competition{
	battles: set Battle,
	creator: one Educator,
	managers: set Educator,
	students: set Student
}

sig Battle{
	participants: set Participant,
	maxNstudentPerTeam: Int
}{
	all t: Team | #t.students <= maxNstudentPerTeam
}
