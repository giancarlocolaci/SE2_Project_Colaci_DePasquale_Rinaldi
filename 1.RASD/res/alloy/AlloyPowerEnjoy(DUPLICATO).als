module PowerEnjoy

//SIG

sig Stringa {}

sig Float {
		leftPart : one Int,
		rightPart : one Int
} {
		leftPart > 0
		rightPart > 0
}

sig Car {
		id : one Int,
		plate : one Stringa,
		wCode : one Int,
		ecs : one ECS,
		ads : one ADS,
		status : one CarStatus//,
		//request : set RMSS
} {
		id > 0
		wCode > 0
}

abstract sig RMSS {
		id : one Int,
		startTime : one Int,
		endTime : lone Int,
		cost : one Float,
		status : one RequestStatus,
		paymentStatus : one PaymentStatus,
		userID : one Int,
		carID : one Int,
		userPosition : one Stringa,
		carPosition : one Stringa,
		car : one Car
		//reservation : lone Reservation,
		//rent : lone Rent
} {
		id > 0
		startTime > 0
		endTime = none or endTime > 0
		userID > 0
		carID > 0
		endTime > startTime
}

sig Reservation extends RMSS {
		countDown : one Int
} {
		countDown >= 0
}

sig Rent extends RMSS {
		mSavingOptionActived : one Bool
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
		id > 0
}

sig DeactivatedUser extends User {}

sig ECS {
		id : one Int,
} {
		id > 0
}

sig ADS {
		id : one Int
} {
		id > 0
}

sig ParkingArea {
		id : one Int,
		name : one Stringa,
		availableCars : one Int,
		car : set Car,
		rechargingArea : set RechargingArea
} {
		id > 0
		availableCars > 0
}

sig City {
		id : one Int,
		name : one Stringa,
		parkingArea : set ParkingArea
} {
		id > 0
}

sig RechargingArea {
		id : one Int,
		plugs : one Int,
		address : one Stringa,
		isSpecial : one Bool
} {
		id > 0
		plugs > 0
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
		#ParkingArea >=  1
}

//  In any parking area there could be zero or more recharging area
fact presenceOfRechargingArea {
		#RechargingArea >=  0
}

//  In any parking area there could be zero or more cars
fact presenceOfCars {
		#Car >= 0
}

// Relation between users and active requests (reservation or rent)
fact atMaxOneActiveRequestForUser {
		(all u : User | lone r : RMSS | (u.request = r) and (r.userID = u.id) and (r.status = ACTIVE))
			// Each user has at maximum an active request at time
}

// Relation between Rent and Reservations
fact a {
		all ren : Rent | one res : Reservation | ( (ren.userID = res.userID) and 
					(ren.carID = res.carID) and (ren.startTime = res.endTime) )
}

// Relation between RMSS and Reservation or Rent
fact relationBetweenRequests {
		(all rm : RMSS | 
								(
								one res : Reservation | ( (rm.id = res.id) and (rm.userID = res.userID)
								and (rm.carID = res.carID) and (rm.startTime = res.startTime) and
								(rm.endTime = res.endTime) )
								)
								or
								(
								one ren : Rent | ( (rm.id = ren.id) and (rm.userID = ren.userID)
								and (rm.carID = ren.carID) and (rm.startTime = ren.startTime) and
								(rm.endTime = ren.endTime) )
								)
		)
}




fact b {
		all ren : Rent | no res : Reservation | ren.id = res.id
}


fact c {
		all res : Reservation | no ren : Rent | res.id = ren.id
}


// Relation between active requests (reservations or rents) and users
fact exactelyOneUserForActiveRequest {
		(all r : RMSS | r.status = ACTIVE implies 
				(one u : User | u.request = r))
			// Each active request belongs exactely to one user
}

// Each user can have multiple expired requests (reservations or rents)
fact multipleExpiredRequests {
		(all r : RMSS | r.status = EXPIRED implies
				(one u : User | u.request = r))
}

// Relation between cars and active requests (reservations or rents)
fact atMaxOneActiveRequestForCar {
		(all c : Car | lone r : RMSS | (c.request = r) and (r.status = ACTIVE))
			// Each car has at maximum an active request at time
}




// Relation between active requests (reservation or rent) and car
fact exactelyOneCarForActiveRequest {
		(all r : RMSS | r.status = ACTIVE implies 
				(one c : Car | c.request = r))
			// Each active request refers exactely to one car
}

// Relation between deactivated users and active requests (reservation or rent) 
fact noActiveRequestForDeactivatedUser {
		(no dU : DeactivatedUser | one r : RMSS | (dU.request = r) and (r.status = ACTIVE))
			// No deactivated users can have an active request
}

// Relation between active requests (reservation or rent) and deactivated users
fact noDeactivatedUserForActiveRequest {
		(all r : RMSS | r.status = ACTIVE implies 
				(no dU : DeactivatedUser | dU.request = r))
			// Each active request does not belong to any deactivated user
}

// No duplicated users
fact noDuplicatedUser {
		(no u1 , u2 : User | u1.id = u2.id and u1 != u2) and 
 		(no u1 , u2 : User | u1.email = u2.email and u1 != u2) and 
		(no u1 , u2 : User | u1.SSN = u2.SSN and u1 != u2) and 
		(no u1 , u2 : User | u1.drivingLicence = u2.drivingLicence and u1 != u2) 
}

// No users with NOTCONFIRMED billing information
fact noUserWithNotConfirmedBilling {
		no u : User | u.billingInformation = NOTCONFIRMED
}

// No duplicated deactivated users
fact noDuplicatedDeactivatedUser {
		(no du1 , du2 : DeactivatedUser | du1.id = du2.id and du1 != du2) and 
 		(no du1 , du2 : DeactivatedUser | du1.email = du2.email and du1 != du2) and 
		(no du1 , du2 : DeactivatedUser | du1.SSN = du2.SSN and du1 != du2) and 
		(no du1 , du2 : DeactivatedUser | du1.drivingLicence = du2.drivingLicence and du1 != du2) 
}

// No cities with the same ID
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

// No duplicated requests
fact noDuplicatedRMSS{
		(no req1 , req2 : RMSS | req1.id = req2.id and req1 != req2) and
		(no req1, req2 : RMSS | req1.userID = req2.userID and
		req1.carID = req2.carID and req1.startTime = req2.startTime
		and req1.endTime = req2.endTime and req1 != req2)
}

fact noDuplicatedReservation{	
		(no res1 , res2 : Reservation | res1.id = res2.id and res1 != res2) and
 		(no res1, res2 : Reservation | res1.userID = res2.userID and
		res1.carID = res2.carID and res1.startTime = res2.startTime 
		and res1.endTime = res2.endTime and res1 != res2)
}

fact noDuplicatedRent{
		(no ren1 , ren2 : Rent | ren1.id = ren2.id and ren1 != ren2) and
		(no ren1, ren2: Rent | ren1.userID = ren2.userID
		and ren1.carID = ren2.carID and ren1.startTime = ren2.startTime
		and ren1.endTime = ren2.endTime and ren1 != ren2)
}

// Users cannot hold the same reservation
// fact noDifferentUsersForTheSameReservation{
//		(all r : RMSS | no u1, u2 : User | u1 !)
//}


// USER -- > RENT : SAME MONEY SAVING OPTION

// No duplicated cars
fact noDuplicatedCars {
		(no c1 , c2 : Car | c1.id = c2.id and c1 != c2) and 
 		(no c1 , c2 : Car | c1.plate = c2.plate and c1 != c2) and 
		(no c1 , c2 : Car | c1.wCode = c2.wCode and c1 != c2)
}

// No ECS with the same ID
fact noDuplicatedECS {
		no ecs1 , ecs2 : ECS | ecs1.id = ecs2.id and ecs1 != ecs2
}

// No ADS with the same ID
fact noDuplicatedADS {
		no ads1 , ads2 : ADS | ads1.id = ads2.id and ads1 != ads2
}

// AVAILABLE car 

// When a request is active the status of the payment is pending
fact pendingPaymentForActiveRequest {
		(all r : RMSS | r.status = ACTIVE implies r.paymentStatus = PENDING)
}
// When a car is RENTED the related RENT is ACTIVE
fact aRentedCarIsRelatedToAnActiveRent {
		(all c : Car |  c.status = INUSE implies 
		(one ren : Rent | c.id = ren.carID and ren.status = ACTIVE) and
		(no res : Reservation | c.id = res.carID and res.status = ACTIVE)
		)
}

fact anActiveRentIsRelatedToARentedCar {
		(all ren : Rent | ren.status = ACTIVE implies
		(one c : Car | ren.carID = c.id and c.status = INUSE)
		)
}

// When a car is RESERVED the related RESERVATION is ACTIVE
fact aReservedCarIsRelatedToAnActiveReservation {
		(all c : Car |  c.status = RESERVED implies 
		(one res : Reservation | c.id = res.carID and res.status = ACTIVE) and
		(no ren : Rent | c.id = ren.carID and ren.status = ACTIVE)
		)
}

fact anActiveReservationIsRelatedToAReservedCar {
		(all res : Reservation | res.status = ACTIVE implies
		(one c : Car | res.carID = c.id and c.status = RESERVED)
		)
}

// When a car is UNAVAILABLE, it cannot be RESERVED
fact noUnavailableReservedCar {
		all c : Car | c.status = UNAVAILABLE implies
		(no res : Reservation | res.status = ACTIVE and res.carID = c.id)
}


// When a car is AVAILABLE, it cannot be RENTED
fact noUnavailableRentedCar {
		all c : Car | c.status = UNAVAILABLE implies
		(no ren : Rent | ren.status = ACTIVE and ren.carID = c.id)
}

// When a reservation is EXPIRED, it still remembers the reserved car
fact consistencyOfReservation {
		(all res : Reservation | res.status = EXPIRED implies
		(one c : Car | res.carID = c.id)
		)
}

// When a rent is EXPIRED, it still remembers the rented car
fact consistencyOfRent {
		(all ren : Rent | ren.status = EXPIRED implies
		(one c : Car | ren.carID = c.id)
		)
}  












// When a car is INUSE the related RENT is ACTIVE
// When a car is AVAILABLE 
// When a car is UNAVAILABLE




//ASSERTION

// The number of active rents is equal to the number of cars in use
assert equalityOfRentedCarsAndActiveRents {
		#{r : Rent | r.status = ACTIVE} = #{c : Car | c.status = INUSE}
}
// check equalityOfRentedCarsAndActiveRents for 8 [no counterexamplefound]

// The number of active reservations is equal to the number of cars reserved
assert equalityOfReservedCarsAndActiveReservations {
		#{r : Reservation | r.status = ACTIVE} = #{c : Car | c.status = RESERVED}
}
// check equalityOfReservedCarsAndActiveReservations for 8 [no counterexamplefound]

// The number of the Reservation is greater or equal to the number of Rent
assert noRentWithoutReservation{
	all u : User |
		#{res: Reservation | res.userID = u.id } >= #{ren : Rent | ren.userID = u.id}
}
//check noRentWithoutReservation for 3

assert z{
		#{rm : RMSS} >= #{res : Reservation}
}

//check z for 8

assert zz{
		#{rm : RMSS} >= #{rn : Rent}
}

//check zz for 3

assert zzz{
		#{res : Reservation} < #{req : RMSS}
}

//check zzz for 2


 pred show {}

run show for 4 but exactly 1 User, exactly 1 RMSS, exactly 2 Car





















