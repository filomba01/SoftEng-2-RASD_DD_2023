open util/boolean

-- ENUMS
-- state of an event such as a competition or a battle
 -- the state of a battle can only evolve as Created -> Started -> Ended
enum EventState {CREATED, STARTED, ENDED}
-- type of possible condition for badges
-- EQUAL: ==, GEQ: >=, LEQ: <= , LT: <, GT: >
enum ConditionType { EQUAL, GEQ, LEQ, LT, GT}
 


-- Generalites such as name, surname 
sig Generalities{}

-- value that can be both Integer, Double or String used for badge conditions
sig GenericValue{}

-- Rule defined by
sig Rule{
	variables: String,
	conditionType: one ConditionType,
	value: one GenericValue
}
-- badges to be assign to a student
sig Badge{
	creator: one Educator,
	conditions: set Rule,
}
-- the rule of a badge

abstract sig User{
	generalities: one Generalities,
	email: String,
	username: String,
	password: String
}

-- extends Users Participant
--extends User
sig Student{
	var competitions: set Competition,
	var badges: set Badge,
}

sig Educator{
	created_badges: set Badge,
	manage_competitions: set Competition,

}

sig Team{
	creator: one Student,
	var teamStudents: some Student,
	team_name: String,
	var joined_battle: set Battle,
	public: Bool,
	var invitedStudents: set Student
}

-- an event describe the time and the state of a competition or a battle (created, started, ended)
sig Event{
	state: one EventState,
	-- start time and end time is supposed to be an integer timestamp
	startTime: Int,
	endTime: Int
}

sig Competition{
	battles: set Battle,
	creator: one Educator,
	managers: some Educator,
	var students: set Student,
	var event: Event,
	startTime: Int,
	endTime: Int
}

sig Battle{
	competition: one Competition,
	-- educators that manages the battle
	creator: one Educator,
	managers: set Educator,
	participants: set Team,
	var event: Event,
	maxNstudentPerTeam: Int,
	minNstudentPerTeam: Int,
	startTime: Int,
	endTime: Int
}


-- PREDICATES
pred starts[ e: Event ] {
	e.state = CREATED
	e.state' = STARTED
	e.startTime' = e.endTime
}

pred ends[ e: Event ] {
	e.state = STARTED
	e.state' = ENDED
	e.startTime' = e.endTime
}
-- add st to competition
pred addStudentToCompetition [s: Student, c: Competition] {
	c.students' = c.students' + s 
}

pred removeStudentToCompetition [s: Student, c: Competition] {
	c.students' = c.students' - s 
}

-- add student to a team
pred addInvitedStudentToTeam [s: Student, t: Team] {
	t.invitedStudents' = t.invitedStudents - s
	t.teamStudents' = t.teamStudents + s 
}

pred addStudentToPubliTeam [s: Student, t: Team] {
	t.teamStudents' = t.teamStudents + s 
}
-- remove a student from a team
pred removeStudentFromTeam [s: Student, t: Team] {
	t.teamStudents' = t.teamStudents' - s 
}
--add student invitation to a team
pred addStudentInvitationFromTeam [s: Student, t: Team] {
	t.invitedStudents' = t.teamStudents' + s 
}

--remove student invitation to a team
pred removeStudentInvitationFromTeam [s: Student, t: Team] {
	t.invitedStudents' = t.teamStudents' - s 
}

-- predicate for a team to be added to a battle
pred addTeamToBattle[t: Team, b: Battle]{
	b.participants' = b.participants' + t
} 
pred removeTeamToBattle[t: Team, b: Battle]{
	b.participants' = b.participants' - t
} 

-- FACTS
-- the state of a competition can only evolve as Created -> Started -> Ended

-- if the state of a event is Started, before it has always been Created
fact eInStarted {
	all e: Event |
	always ( 
		e.state = STARTED
		implies
		(
			once starts[e] and always ( e.state = STARTED or e.state = ENDED )
		)
	)
}
-- if the state of a event is Ended state, then it ended
fact eInEnded {
	all e: Event |
	always ( 
		e.state = ENDED
		implies(
			once ends[e] and always ( e.state = ENDED )
		)
		 
	)
}
-- if the state of an event is Created, before it has always been Created
fact eInCreated {
	all e: Event |
	always ( 
		e.state = CREATED
		implies (
			historically e.state = CREATED and always (e.state = STARTED or e.state = ENDED)
		)
	)
}

-- a student can be added to a competition only if its state is Created and it is no part of the competition
fact addStToCompetitionOnlyIffCreated{
	all s : Student, c: Competition |
		addStudentToCompetition[s,c] iff ( c.event.state = CREATED and !(s in c.students) )
}

-- a student can be removed to a competition only if its state is Created and it is part of the competition
fact removeStToCompetitionOnlyIffCreated{
	all s : Student, c: Competition |
		removeStudentToCompetition[s,c] iff (c.event.state = CREATED and (s in c.students) )
}

-- ???? WHEN A STUDENT CAN BE REMOVED BY A COMPETITION ????


-- a battle can only start and end inside the timespan of a competition
fact battleHappensInsideTheCompetitionTime{
	all b : Battle, c: Competition |
		b in c.battles implies (
			b.startTime >= c.startTime and b.endTime <= c.endTime 
		)
}

-- a battle cannot be part of more than one competition
fact battleAssignedToOnlyaCompetition{
	all b: Battle, c1: Competition |
		(
			(b in c1.battles) 
			implies 
			no c2: Competition | ( b in c2.battles and c2 != c1 ) 
		)
}	

-- CAN BATTLE OVERLAP IN THE SAME COMPETITION?

-- a battle is part a competition only if the competition contain the battle
fact battleiffCompetition{
	all b:Battle, c: Competition | 
		b.competition = c iff  b in c.battles
}
-- An educator can create a battle only if it manages the competition inside that battle
fact edManageBattleiffManageCompetition{
	all e : Educator, c: Competition, b: Battle |
		(e in b.creator or e in b.managers and b in c.battles) implies (e in c.managers) 
}
-- a battle can be joined by a team only if is not already started
fact addTeamToBattleOnlyIffCreated{
	all t : Team, b: Battle |
		addTeamToBattle[t,b] iff ( b.event.state = CREATED and !(t in t.teamStudents) and  t.teamStudents in b.competition.students)
}

fact removeTeamToBattleOnlyIffCreated{
	all s : Student, c: Competition |
		removeStudentToCompetition[s,c] iff (c.event.state = CREATED and (s in c.students) )
}
-- a team part of a battle as always a number of member that matches the constraints
fact nOfStudentPerTeamMatchBattleConstrains{
	all b: Battle | (
		#b.participants.students <= b.maxNstudentPerTeam	
		and
		#b.participants.students >= b.minNstudentPerTeam
	) 
}

-- a student invited in a team cannot be part of it
fact invitedStudentNoPartOfTeam{
	all s : Student, t: Team |
		s in t.invitedStudents implies not( s in t.teamStudents)  
}

-- a student can join a team by its own only if is public
fact studentJoinAutonoumuslyOnlyPublicTeams{
	all s : Student, t: Team |
		addStudentToPubliTeam[s,t] implies (
				t.public in True
				and no b : Battle | t in b.participants and b.event.state != CREATED
				)  
}

-- a student cannot join a team which is not public if is not invited
fact onlyInvitedStudentsJoinsPrivateTeams{
	all s : Student, t: Team |
		addInvitedStudentToTeam[s,t] 
		implies (
				s in t.teamStudents 
				and no b : Battle | t in b.participants and b.event.state != CREATED
				)  
}
-- a student can be removed by a team only if is part of it
fact onlyStudentsPartOfTheTeamCanBeRemoved{
	all s : Student, t: Team |
		removeStudentFromTeam[s,t] 
		implies (
				s in t.teamStudents 
				and no b : Battle | t in b.participants and b.event.state != CREATED
				)  
}
-- a student invitation can be removed in a team only if the student has been invited to the team
-- once a student join a team after an invitation, the student in no more part of the set of the invitation
-- once a team is part of a battle it cannot be modified no more
-- if a student is the owner of a team it cannot be removed by its team
-- an owner of a team is always part of the team (students)


-- a badge of a certain competition can be assigned only to student inside the competition
-- a badge for a competition can be created by an educator that manages it (lead it or simpy manage?)
