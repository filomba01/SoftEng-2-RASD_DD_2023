open util/boolean
-- ENUMS
-- state of a team
enum TeamState{ WAITING, READY}

-- Generalites such as name, surname 
sig Generalities{}

sig Badge{
	--conditions: some Rule,
}

sig Name{}
sig Username{}
sig Email{}

abstract sig User{
	generalities: Generalities,
	username: Username,
	email: Email
	
}

sig Student extends User{
	competitions: set Competition,
	badges: set Badge,
	team: lone Team
}

sig Educator extends User{
	created_badge: set Badge,
	manage_competition: set Competition,
	manage_battle: set Battle,
	manual_evalutions: set ManualEvalutation
}

sig Team{
	teamStudents: some Student,
	team_name: Name,
	joined_battle: one Battle,
	teamState: one TeamState,
	public: Bool,
	invitedStudents: set Student,
	points: set Point
}

abstract sig TimeEvent{
	startTime: Int,
	endTime: Int
}{
	startTime < endTime
}

sig Competition extends TimeEvent{
	battles: set Battle,
	name: Name,
	managers: some Educator,
	students: set Student,
	badges: set Badge,
	
}

sig Battle extends TimeEvent{
	name: Name,
	-- educators that manages the battle
	manager: set Educator,
	participant: set Team,
	evaluations: set Point,
	maxNstudentPerTeam: Int,
	minNstudentPerTeam: Int,

}

sig PointValue{}

abstract sig Point{
	value: one PointValue
}

sig ManualEvalutation extends Point{}

sig AutomaticEvaluation extends Point{}

sig SATEvaluation extends Point{}


----------------
-- PREDICATES --
----------------

pred UserSameMail[u1:User,u2:User]{
	u1.email = u2.email 
}

pred UserSameUsername[u1:User,u2:User]{
	u1.username = u2.username 
}

pred CompetitionSameName[c1:Competition,c2:Competition]{
	c1.name = c2.name
}

-----------
-- FACTS --
-----------

-- two different users cannot have same mail
fact UserCannotHaveSameMail{
	all disj u1,u2 : User |
		!UserSameMail[u1,u2]
}
-- two different users cannot have the same username
fact UserCannotHaveSameUsername{
	all disj u1,u2 : User |
		!UserSameUsername[u1,u2]
}

-- two different competitions cannot have the same name
fact CompetitionCannotHaveSameName{
	all disj c1,c2 : Competition |
		!CompetitionSameName[c1,c2]
}
-- there is no Competition which is not created by an educator
fact aCompetitionIsAlwaysCreatedByAnEducator{
	all c: Competition |
		one e: Educator |
			c in e.manage_competition 
}


-- if a student is in a competition, then the competition contains that student
fact studentInsideCompetitionIffCompetitionContainsit{
	all c: Competition, s: Student |
		c in s.competitions iff s in c.students   
}

-- there is no badges which is not created by an educator
fact aBadgeIsAlwaysCreatedByAnEducator{
	all b: Badge |
		one e: Educator |
			b in e.created_badge 
}

-- a battle is part of an only competition
fact battleOnlyInOneCompetition{
	all b: Battle, c1:Competition |
		b in c1.battles implies
			no c2: Competition |
				b in c2.battles and c2 != c1 
}

-- a battle is always linked to a competition
fact battleAlwaysInCompetition{
	all b: Battle |
		one c: Competition |
				b in c.battles 
}


-- a battle starts and ends always inside a competition
fact battleTimeInsideItsCompetition{
	all c: Competition |
		all bc: c.battles |
			bc.startTime > (c.startTime - 1) and bc.endTime < (c.endTime + 1) 
}

-- if a badge is created by an Educator, is uniqe and is its creator
fact badgeCreatedByOnlyOneEducator{
	all b: Badge, e: Educator | 
		b in e.created_badge 
			implies 
			no e2: Educator | 
				b in e2.created_badge and e != e2
}
-- a badge is always part of one competition
fact badgeAlwaysAssignedToCompetition{
	all b: Badge |
		one c: Competition |
			b in c.badges
}

-- a badge is assigned to a student only if it participated to the competition where the badge
-- has been assigned
fact studentsEarnsBadgesInsideRightCompetition{
	all b:Badge, s:Student |
		b in s.badges
		implies
			one cs : s.competitions |
				b in cs.badges

}
-- a badge created by an Educator is always part of a competition MANAGED by the same educator
fact badgeCreatedByEdAreInsideCompetitionManagedByHim{
	all b: Badge, e: Educator | 
		b in e.created_badge 
			implies 
		b in e.manage_competition.badges
}

-- same as above for battles
-- a badge created by an Educator is always part of a competition MANAGED by the same educator
fact battlesCreatedByEdAreInsideCompetitionManagedByHim{
	all b: Battle, e: Educator | 
		b in e.manage_battle
		iff 
		b in e.manage_competition.battles
}


-- a team is part on only one Battle
fact teamOnlyInOneBattle{
	all t: Team, b: Battle |
		t in b.participant
		implies
		no b2: Battle |
			b2 != b and t in b2.participant 
}

-- a student can be part of only a team
fact StudentPartOfOnlyaTeam{
	all t:Team, s:Student | 
		t = s.team iff s in t.teamStudents
}

-- student are part of a team that battle in a competition they are part of
fact StudentPartOfTeamInsideTheSameCompetition{
	all s:Student, t:Team |
		t = s.team implies
		t in s.competitions.battles.participant
}


-- no invited students are part of the team --
fact StudentInvitedNotInsideTeam{
	all s:Student, t:Team |
		t = s.team implies not (s in t.invitedStudents)
}

-- POINTSSSSSS ---

-- every team which has been part of a competition (ENDED??)
-- has an automatic point, a sat point and can have a manual
-- evaluation
fact teamHasConsistentPoints{
	all b:Battle, t:Team |
		t in b.participant implies 
			one ae: AutomaticEvaluation | ae in t.points
			and
			one sate: SATEvaluation | sate in t.points
			and
			lone me : ManualEvalutation | me in t.points
}
--

-- educators can evaluate only inside a battle they manage
fact educatorsCanEvaluateOnlyInsideABattleTheyManage{
	all e: Educator, b: Battle |
		b.evaluations in e.manual_evalutions implies
			b in e.manage_battle
}

-- only educators that manage a battle can assign manual evaluation to a student
fact teamManualEvaluationsAreGivenByConsistentsEducators{
	all e: Educator, t: Team | 
		all i : t.points & e.manual_evalutions |
			i in t.joined_battle.evaluations
		
}

-- all points are assigned inside a battle
fact allPointsAssigendInBattle{
	all p: Point | 
		one b: Battle |
			p in b.evaluations
}

-- all points are assigned to a team and are assigend inside the battle
-- they are part of
fact allPointsAssigendToTeam{
	all p: Point | 
		one t: Team |
			p in t.points and p in t.joined_battle.evaluations
}

--there is no manual evaluation not assigned to an educator
fact manualEvaluationIsAlwaysMadeByanEducator{
	all me: ManualEvalutation | 
		one e: Educator | 
			me in e.manual_evalutions and
			me in e.manage_battle.evaluations
}

pred show{
	#Student > 1 
	#Badge > 1  #Student.badges > 3
	#Competition > 1
	#Team > 1
	#Educator > 2
	#Team.invitedStudents > 1
	#Team.teamStudents > 2
}

run show for 10
