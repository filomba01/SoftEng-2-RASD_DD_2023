open util/boolean

-- ENUMS
-- state of an event such as a competition or a battle
 -- the state of a battle can only evolve as Created -> Started -> Ended
enum EventState {CREATED, STARTED, ENDED}
-- type of possible condition for badges
-- EQUAL: ==, GEQ: >=, LEQ: <= , LT: <, GT: >
--enum ConditionType { EQUAL, GEQ, LEQ, LT, GT}
-- state of a team
enum TeamState{ WAITING, READY}


-- Generalites such as name, surname 
sig Generalities{}

-- value that can be both Integer, Double or String used for badge conditions
sig GenericValue{}

-- Rule defined by
sig Rule{
	variables: String,
	--conditionType: one ConditionType,
	--value: one GenericValue
}
-- badges to be assign to a student
sig Badge{
	creator: one Educator,
	conditions: some Rule,
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
	var team: one Team
}

sig Educator{
	created_badges: set Badge,
	manage_competitions: set Competition,

}

sig Team{
	creator: one Student,
	var teamStudents: some Student,
	team_name: String,
	var joined_battle: one Battle,
	var teamState: one TeamState,
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
	var battles: set Battle,
	name: String,
	creator: one Educator,
	var managers: some Educator,
	var students: set Student,
	var event: Event,
	startTime: Int,
	endTime: Int
}

sig Battle{
	competition: one Competition,
	name: String,
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

pred addManagerToCompetition[e: Educator, c: Competition]{
	c.managers' = c.managers + e
}

pred removeManagerFromCompetition[e: Educator, c: Competition]{
	c.managers' = c.managers - e
}


pred addManagerToBattle[e: Educator, b: Battle]{
	b.managers' = b.managers + e
}

pred removeManagerFromBattle[e: Educator, b: Battle]{
	b.managers' = b.managers - e
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


-- there is no competition with the same name
fact noCompetitionWithSameName{
	all c1: Competition, c2: Competition | (
		c1.name != c2.name and c1 != c2
	) 
}

-- a student can be added to a competition only if its state is Created and it is no part of the competition
fact addStToCompetitionOnlyIfCreated{
	all s : Student, c: Competition |
		addStudentToCompetition[s,c] implies ( c.event.state = CREATED and !(s in c.students) )
}

-- a student can be removed to a competition only if its state is Created and it is part of the competition
fact removeStToCompetitionOnlyIfCreated{
	all s : Student, c: Competition |
		removeStudentToCompetition[s,c] implies (c.event.state = CREATED and (s in c.students) )
}


-- a battle can only start and end inside the timespan of a competition
fact battleHappensInsideTheCompetitionTime{
	all b : Battle, c: Competition |
		b in c.battles implies (
			b.startTime > c.startTime - 1 and b.endTime < c.endTime + 1
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
-- we assume that is legal to two battle to overlap in a competition

-- a battle is part a competition only if the competition contain the battle
fact battleiffCompetition{
	all b:Battle, c: Competition | 
		b.competition = c iff  b in c.battles
}
-- An educator can create a battle only if it manages the competition inside that battle
--fact edManageBattleifManageCompetition{
--	all e : Educator, c: Competition, b: Battle |
--		(e in b.creator or e in b.managers and b in c.battles) implies (e in c.managers) 
--}
-- an educator can manage a battle only if is part of the competition
fact edManageBattleifManageCompetition{
	all e : Educator, c: Competition, b: Battle |
		 addManagerToCompetition[e, c] implies ((e in b.creator or e in b.managers) and b in c.battles) 
}

-- a battle can be joined by a team only if is not already started
fact addTeamToBattleOnlyIfCreated{
	all t : Team, b: Battle |
		addTeamToBattle[t,b] implies ( b.event.state = CREATED and !(t in b.participants) and  t.teamStudents in b.competition.students)
}

fact removeTeamToBattleOnlyIfCreated{
	all s : Student, c: Competition |
		removeStudentToCompetition[s,c] implies (c.event.state = CREATED and (s in c.students) )
}

-- a team part of a battle as always a number of member that matches the constraints
fact nOfStudentPerTeamMatchBattleConstrains{
	all b: Battle, t: Team | (
		(t in b.participants) implies
		#t.teamStudents < b.maxNstudentPerTeam + 1	
		and
		#t.teamStudents > b.minNstudentPerTeam - 1
	) 
}

-- a student can be part of only a team
fact studentInOnlyOneTeam{
	all s: Student, t: Team |
		s in t.teamStudents implies 
	no t2 : Team |
		s in t2.teamStudents and t2 != t
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
				--and no b : Battle | t in b.participants and b.event.state != CREATED
				)  
}

-- a student cannot join a team which is not public if is not invited
fact onlyInvitedStudentsJoinsPrivateTeams{
	all s : Student, t: Team |
		addInvitedStudentToTeam[s,t] 
		implies (
				s in t.invitedStudents 
				--and no b : Battle | t in b.participants and b.event.state != CREATED
				)  
}
-- a student can be removed by a team only if is part of it
fact onlyStudentsPartOfTheTeamCanBeRemoved{
	all s : Student, t: Team |
		removeStudentFromTeam[s,t] 
		implies (
				s in t.teamStudents 
				and t.public in False
				and no b : Battle | t in b.participants and b.event.state != CREATED
				)  
}


-- a student invitation can be removed in a team only if the student has been invited to the team
-- once a student join a team after an invitation, the student in no more part of the set of the invitation
-- once a team is part of a battle it cannot be modified no more
-- if a student is the owner of a team it cannot be removed by its team
-- an owner of a team is always part of the team (students)

-- if a badge is created by an Educator, is uniqe and is its creator
fact badgeCreatedByOnlyOneEducator{
	all b: Badge, e: Educator | 
		b.creator = e implies no e2: Educator | b.creator = e2
}
-- badge creator has created that badge
fact badgeCreatorHasCreatedThatBadge{
	all b: Badge, e: Educator | 
		b.creator = e iff b in e.created_badges 
}
-- a badge of a certain competition can be assigned only to student inside the competition
-- a badge for a competition can be created by an educator that manages it (lead it or simpy manage?)
pred show [s:Student]{
	#s.badges = 0; #s.badges = 1;
}


run show for 1 but 5 Student for 3 steps
