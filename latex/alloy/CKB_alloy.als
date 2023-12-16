open util/boolean
-----------
-- ENUMS --
-----------
-- state of a team
enum TeamState{ WAITING, READY}

enum BattleState{CREATED,STARTED,ENDED}
-- type of possible condition for badges
-- EQUAL: ==, GEQ: >=, LEQ: <= , LT: <, GT: >
enum ConditionType { EQUAL, GEQ, LEQ, LT, GT}

-----------
-- SIG --
-----------
-- value that can be both Integer, Double or String used for badge conditions
sig GenericValue{}
-- Generalites such as name, surname 
sig Generalities{}
sig Name{}
sig Username{}
sig Email{}
sig GitHubLink{}
-- a rule can be also created without a badge assignation?
sig Rule{
	variables: Name,
	conditionType: one ConditionType,
	value: one GenericValue
}

sig Badge{
	conditions: some Rule,
}


abstract sig User{
	generalities: Generalities,
	username: Username,
	email: Email
	
}

sig Student extends User{
	competitions: set Competition,
	badges: set Badge,
	team: set Team
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
	link: lone GitHubLink,
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
	link: one GitHubLink,
	manager: set Educator,
	participant: set Team,
	evaluations: set Point,
	battleState: one BattleState,
	maxNstudentPerTeam: Int,
	minNstudentPerTeam: Int,

}{
	--the min number of student is always less than equal than the max
	minNstudentPerTeam > 0 and
	minNstudentPerTeam < (maxNstudentPerTeam + 1)
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

pred TeamSameName[t1:Team,t2:Team]{
	t1.team_name = t2.team_name
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

-- two different teams cannot have the same name
fact TeamCannotHaveSameName{
	all disj t1,t2 : Team |
		!TeamSameName[t1,t2]
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

-- a badge is always linked

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

-- if a team is in a battle it has joined it
fact teamInBattleParticipantIffTeamJoinedBattle{
	all t: Team, b: Battle |
		t in b.participant iff t.joined_battle = b
}

--@toFix could be redundant if above true
-- a team is part on only one Battle
fact teamOnlyInOneBattle{
	all t: Team, b: Battle |
		t in b.participant
		implies
		no b2: Battle |
			b2 != b and t in b2.participant
}
-- a student is part of battles only if are in the same competition
fact stdInsideBattleInConsistentCompetition{
	all s: Student, c: Competition | 
		s.team.joined_battle in c.battles
		iff c in s.competitions
}

-- a team part of a battle respects its number constraints
fact teamCapacityRespectBattleConstraints{
	all t: Team, b: Battle | 
		t in b.participant
		implies
			(
				#t.teamStudents > b.minNstudentPerTeam - 1
				and 
				#t.teamStudents < b.maxNstudentPerTeam + 1
			)
}
-- battles have all different github links
fact noSameGitHubLinksBattles{
	all disj b1,b2: Battle|
		b1.link != b2.link

}

-- teams have all different github links
fact noSameGitHubLinksBattles{
	all disj t1,t2: Team|
		t1.link != t2.link

}

-- a student can be part of only a team
fact StudentPartaTeamiffTeamHasStudent{
	all t:Team, s:Student | 
		t in s.team iff s in t.teamStudents 
		
}
-- a student cannot be part of two teams in the same battle
fact StudentPartOnlyOfATeamInsideABattle{
	all t:Team, s:Student | 
		t in s.team
			implies
				#(t.joined_battle.participant & s.team) = 1 
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


-- a team is in waiting on a battle only if the battle is not started
fact teamInWaitingOnlyInBattleNotStarted{
	all b:Battle |
		b.battleState != CREATED implies
		(no t:Team | 
			t.joined_battle = b and t.teamState = WAITING)
}
-- POINTS ---

-- every team which has been part of a ended competition
-- has an automatic point, a sat point and can have a manual
-- evaluation
fact teamHasConsistentPoints{
	all b:Battle, t:Team |
		(t in b.participant and b.battleState = ENDED) 
		implies 
			one ae: AutomaticEvaluation | ae in t.points
			and
			one sate: SATEvaluation | sate in t.points
			and
			lone me : ManualEvalutation | me in t.points

}
--no one shares the same evaluation
fact noSameEvaluation{
	all disj t1,t2 : Team |
		#(t1.points & t2.points) = 0

}

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

----------------
-- ASSERTIONS --
----------------

-- there is no student in a battle inside competitions which
-- are not joined by the student
assert noStudentInABattleInCompetitionNotJoined{
	all s: Student |
		no c: Competition | 
			#(s.team.joined_battle) > 0 and
			s.team.joined_battle in c.battles 
			and s not in c.students		
}
-- no battle started with a team not ready inside
assert noStartedBattleWithWaitingTeams{
	all b: Battle, t: Team |
		(t in b.participant and b.battleState = STARTED)
			implies
			t.teamState = READY
}
-- there is no student inside a two team in the same
-- battle
assert noStudentInsideABattleWith2Teams{
	all s:Student, t1: Team , t2: Team |
		 t1 in s.team and 
		 t2 in s.team and
		 t2 != t1
		implies
			t2.joined_battle != t1.joined_battle 

}

assert allFinishedBattleGavePointsToTeams{
	all b: Battle |
		b.battleState = ENDED 
		implies 
		no t: b.participant |
			#(b.evaluations & t.points) = 0
}

-- no badge assigned in student not joined a competition
assert noBadgeAssignedToStudentOutsideTheCompetition{
	all s: Student |
		s.badges in s.competitions.badges
}


-- @toAdd
-- Battle can't start if there are not enough teams / at least one team 

-- @toAdd
-- Each competition has at least one manager

-- @toAdd
-- No student is part of a team and an invited student simultaneously

-- @toAdd
-- Each badge has at least one rule

-- @toAdd
-- Each AutomaticEvaluation and SATEvaluation is linked only to a team

-- @toDiscuss
-- Distinction between educator that created the competion and educator that manage the competion
-- For instance an educator that created the competion could add or remove another educator to manage the competion

-- @toAdd
-- Can't exist a team that has not student inside

-- @toAdd
-- Maximum number of students per team is grater than minimum number of students per team



--check noStudentInABattleInCompetitionNotJoined
--check noStartedBattleWithWaitingTeams
--check noStudentInsideABattleWith2Teams
check allFinishedBattleGavePointsToTeams
check noBadgeAssignedToStudentOutsideTheCompetition
----------------
--	  RUN	  --
----------------
pred show{
	#BattleState > 1
	#Student > 2 
	#Badge = 1  
	#Student.badges = 0
	#Competition = 2
	#Team > 2
	#Battle > 2
	#Educator >2
	--#Team.invitedStudents > 1
	--#Team.teamStudents > 0
	#Student.team > 2
	some t: Team | t.teamState = WAITING
}

run show for 10
