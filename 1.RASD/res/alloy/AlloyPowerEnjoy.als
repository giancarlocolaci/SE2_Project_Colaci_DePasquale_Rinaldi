module PowerEnjoy

//SIG

sig Stringa {}

sig Float {
		leftPart : one Int,
		rightPart : one Int
} {
		rightPart >= 0
} 

sig User {
		id : one Int,
		name : one Stringa,
		surname : one Stringa,
		email : one Stringa,
		password : one Stringa,
		phone : one Stringa,
		address : one Stringa,
		SSN : one Stringa,
		verificationCode : one Stringa,
		drivingLicence : one Stringa,
		billingInformation: one BillingInformation,
		moneySavingOption : one Bool,
		request : set RMSS
} {
		id >= 0
}

sig Car {
		id : one Int,
		plate : one Stringa,
		wCode : one Int,
		ads : one ADS,
		location: one Location,
		status : one CarStatus
} {
		id >= 0
		wCode >= 0
}

abstract sig RMSS {
		id : one Int,
		startTime : one Int,
		endTime : one Int,
		cost : one Float,
		status : one RequestStatus,
		paymentStatus : one PaymentStatus,
		userID : one Int,
		userPosition : one Stringa,
		carPosition : one Stringa,
		mSavingOption : one Bool,
		car : one Car,
		user : one User,
		events : set Event
} {
		id >= 0
		startTime >= 0
		endTime >= 0
		endTime = none or endTime >= 0
		userID >= 0
		endTime >= startTime
}

sig Reservation extends RMSS {}

sig Rent extends RMSS {}

sig DeactivatedUser extends User {}

sig ADS {
		id : one Int
} {
		id >= 0
}

abstract sig Event {
	id : one Int,
	status: one Stringa,
	rmss: one RMSS
} {
	id >= 0
}

sig Payment extends Event {}

sig Notification extends Event {
	message: one Stringa
}

abstract sig Location {
	id : one Int,
	boundaries : set Int,
	latitude : one Float,
	longitude : one Float
} {
	id >= 0
	latitude.leftPart >= 0
	longitude.leftPart >= 0
}

sig City extends Location {
	name : one Stringa,
	zipCode : one Int,
	parArea : set ParkingArea
} {
		zipCode > 0
}

sig ParkingArea extends Location {
	availableCars : one Int,
	rechargingArea : one RechargingArea
} {
	availableCars >= 0
}

sig RechargingArea extends Location {
		plugs : one Int,
		ranking : one Int,
		maxRadius : one Int,
		isSpecial : one Bool
} {
		plugs >= 0
		ranking >= 0
		maxRadius >= 0
}

// ENUMS

enum Bool {
		TRUE,
		FALSE
}

enum BillingInformation {
		CONFIRMED,
		NOTCONFIRMED
}

enum PaymentStatus {
		ACCEPTED,
		PENDING,
		DENIED
}

enum CarStatus {
		AVAILABLE,
		RESERVED,
		UNAVAILABLE,
		INUSE
}

enum RequestStatus {
		ACTIVE,
		EXPIRED
}

// FACTS

//  In any city there is at least a parking area
fact atLeastAParkingArea {
		(all c : City | #c.parArea >=  1)
}


//  In any parking area there could be zero or more recharging area
fact presenceOfRechargingArea {
		(all p : ParkingArea | #p.rechargingArea >=  0)
}

//  In any parking area there could be zero or more cars
fact presenceOfCars {
		(all p : ParkingArea | #p.availableCars >= 0)
}

// No ADS with the same ID
fact noDuplicatedADS {
		(no ads1 , ads2 : ADS | ads1.id = ads2.id and ads1 != ads2)
}


// The same ADS cannot be used by two different Cars
fact theSameADSCannotBeUsedByDifferentCars {
		(no disj c1, c2 : Car | c1.ads = c2.ads)
}

// No Duplicated Users
fact noDuplicatedUser {
		(no u1 , u2 : User | u1.id = u2.id and u1 != u2) and 
 		(no u1 , u2 : User | u1.email = u2.email and u1 != u2) and 
		(no u1 , u2 : User | u1.SSN = u2.SSN and u1 != u2) and 
		(no u1 , u2 : User | u1.drivingLicence = u2.drivingLicence and u1 != u2) 
}

// A reservation and its associated rent have the same user
fact noPhantomResRent {
	(all c : Car |  c.status = INUSE implies
		(no res : Reservation, ren : Rent | res.car = c and ren.car = c and res.user != ren.user)
	)
}

// No rent is possible if the reservation payment was denied or pending
fact noRentIfPaymentUncertain {
	(all c : Car, res : Reservation| c.status = INUSE and res.car = c and (res.paymentStatus = DENIED or res.paymentStatus = PENDING) implies 
		(no ren : Rent | ren.car = c)
	)
}

// No Users with NOTCONFIRMED Billing Information
fact noUserWithNotConfirmedBilling {
		no u : User | u.billingInformation = NOTCONFIRMED
}

// Every rent starts after every reservation
fact noEarlyRent {
	(all c : Car, res : Reservation, ren : Rent | c.status = INUSE and res.car = c and ren.car = c implies
		ren.startTime >= res.endTime 
	)
}

// No Cities with the same ID
fact noDuplicatedCities {
		no c1 , c2 : City | c1.id = c2.id and c1 != c2
}

// No Parking Areas with the same ID
fact noDuplicatedParkingAreas {
		no pa1 , pa2 : ParkingArea | pa1.id = pa2.id and pa1 != pa2
}

// No Recharging Areas with the same ID
fact noDuplicatedRechargingAreas {
		no ra1 , ra2 : RechargingArea | ra1.id = ra2.id and ra1 != ra2
}

// No Duplicated Requests
fact noDuplicatedRMSS {
		(no req1 , req2 : RMSS | req1.id = req2.id and req1 != req2) and
		(no req1, req2 : RMSS | req1.userID = req2.userID and
		req1.car = req2.car and req1.startTime = req2.startTime
		and req1.endTime = req2.endTime and req1 != req2)
}

// No Duplicated Cars
fact noDuplicatedCars {
		(no c1 , c2 : Car | c1.id = c2.id and c1 != c2) and 
 		(no c1 , c2 : Car | c1.plate = c2.plate and c1 != c2) and 
		(no c1 , c2 : Car | c1.wCode = c2.wCode and c1 != c2)
}

// When a car is RENTED the related RENT is ACTIVE and viceversa
fact aRentedCarIsRelatedToAnActiveRent {
		(all c : Car |  c.status = INUSE implies 
		(one ren : Rent | ren.car = c and ren.status = ACTIVE) and
		(no res : Reservation | res.car = c and res.status = ACTIVE) )
		and
		(all ren : Rent | ren.status = ACTIVE implies
		(one c : Car | ren.car = c and c.status = INUSE)
		)
}

// When a car is RESERVED the related RESERVATION is ACTIVE and viceversa
fact aReservedCarIsRelatedToAnActiveReservation {
		(all c : Car |  c.status = RESERVED implies 
		(one res : Reservation | res.car = c and res.status = ACTIVE) and
		(no ren : Rent | ren.car = c and ren.status = ACTIVE)
		) and
		(all res : Reservation | res.status = ACTIVE implies
		(one c : Car | res.car = c and c.status = RESERVED)
		)
}

// When a car is UNAVAILABLE, it cannot be RESERVED nor RENTED
fact noUnavailableReservedCar {
		all c : Car | c.status = UNAVAILABLE implies (
		(no res : Reservation | res.status = ACTIVE and res.car = c) and
		(no ren : Rent | ren.status = ACTIVE and ren.car = c)
	)
}

// When a request is ACTIVE the status of the payment is PENDING
fact pendingPaymentForActiveRequest {
		(all r : RMSS | r.status = ACTIVE implies r.paymentStatus = PENDING)
}

// There are no duplicate payments
fact noDuplicatePayments {
	(all r1, r2 : RMSS | r1 != r2 and r1.paymentStatus = PENDING and r2.paymentStatus = PENDING implies
		(all p1, p2 : Payment | p1 != p2 and p1 in r1.events and p2 in r2.events)	
	)
}
// No Multiple Users for the same Request
fact  noMultipleUsersForTheSameRequest {
		 no disj u1, u2 : User | u1.request & u2.request != none
}

// The same Request cannot be performed by two different User
fact noDifferentUserForTheSameRequest {
		(all u1, u2 : User | u1 != u2 implies
			(no r : RMSS | r in u1.request and r in u2.request)
		)
}

// The same User cannot have two ACTIVE Requests
fact theSameUserCannotPerformTwoActiveRequests {
		no disj r1, r2 : RMSS | r1.user = r2.user and
					r1.status = ACTIVE and r2.status = ACTIVE 
}

// The same User cannot start two Request contemporary
fact noSimultaneousActions {
		no disj r1, r2 : RMSS | r1.user = r2.user and r1.startTime =  r2.startTime
}

// Relation between deactivated users and active requests (reservation or rent) 
fact noActiveRequestForDeactivatedUser {
		(all dU : DeactivatedUser | no r : dU.request | (r.status = ACTIVE))
			// No deactivated users can have an active request
}

//Consistency of the MoneySavingOption for the ACTIVE Requests
fact consistencyOfMoneySavingOptionForActiveRequests {
		(all u : User | u.request.status = ACTIVE implies
				u.moneySavingOption = u.request.mSavingOption) 
}

// A Rent is possible only as a consequence of a Reservation
fact rentIsAPossibleConsequenceOfReservation{
		(all r : Rent | one res : Reservation | res in r.user.request and
							 r.startTime = res.endTime and r.car = res.car)
}



// ASSERTIONS

/******* WORKING *******/							//[no counterexamplefound]
// The number of active rents is equal to the number of cars in use
assert equalityOfRentedCarsAndActiveRents {
		#{r : Rent | r.status = ACTIVE} = #{c : Car | c.status = INUSE}
}
// check equalityOfRentedCarsAndActiveRents for 10

/******* WORKING *******/							//[no counterexamplefound]
// The number of active reservations is equal to the number of cars reserved
assert equalityOfReservedCarsAndActiveReservations {
		#{r : Reservation | r.status = ACTIVE} = #{c : Car | c.status = RESERVED}
}
// check equalityOfReservedCarsAndActiveReservations for 10 

/******* WORKING *******/							//[no counterexamplefound]
//The number of the Reservation is greater or equal to the number of Rent
assert noRentWithoutReservation {
		all u : User |
		#{res: Reservation | res.user = u } >= #{ren : Rent | ren.user = u}
}
// check noRentWithoutReservation for 10 

/******* WORKING *******/							//[no counterexamplefound]
//If there is an end time for a Reservation, that must be after the start
assert requestTimeConsistency {
		all r : RMSS | r.endTime > 0 implies r.endTime > r.startTime 
}
// check requestTimeConsistency for 10



pred show {
		#User >= 2
		#DeactivatedUser = 1
		#RMSS >= 2
		#Car = 3
		#{ r : RMSS | r.status = ACTIVE} >= 1
		#{ r : Rent | r.status = ACTIVE} >= 1
}

run show for 3
