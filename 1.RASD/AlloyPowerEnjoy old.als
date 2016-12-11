module PowerEnjoy

//SIG

sig Stringa {}

sig Float {
		leftPart : one Int,
		rightPart : one Int
}

sig Car {
		id : one Int,
		plate : one Stringa,
		wCode : one Int,
		ecs : one ECS,
		ads : one ADS,
		status : one CarStatus,
		request : set Request
} {
		id > 0
		wCode > 0
}

sig Request {
		id : one Int,
		startTime : one Int,
		endTime : lone Int,
		cost : one Float,
		status : one RequestStatus,
		paymentStatus : one PaymentStatus,
		userID : one Int,
		carID : one Int
} {
		id > 0
		startTime > 0
		endTime = none or endTime > 0
		userID > 0
		carID > 0
}

sig Reservation extends Request {}

sig Rent extends Request {
		moneySavingOptionActived : one Bool,
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
		request : set Request
} {
		id > 0
}

sig DeactivatedUser extends User {}

sig RMSS{
		userPosition : one Stringa,
		carPosition : one Stringa
}

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
		(all u : User | lone r : Request | (u.request = r) and (r.userID = u.id) and (r.status = ACTIVE))
			// Each user has at maximum an active request at time
}

// Relation between active requests (reservation or rent) and users
fact exactelyOneUserForActiveRequest {
		(all r : Request | r.status = ACTIVE implies 
				(one u : User | u.request = r))
			// Each active request belongs exactely to one user
}

// Relation between cars and active requests (reservation or rent)
fact atMaxOneActiveRequestForCar {
		(all c : Car | lone r : Request | (c.request = r) and (r.status = ACTIVE))
			// Each car has at maximum an active request at time
}

// Relation between active requests (reservation or rent) and car
fact exactelyOneCarForActiveRequest {
		(all r : Request | r.status = ACTIVE implies 
				(one c : Car | c.request = r))
			// Each active request refers exactely to one car
}

// Relation between deactivated users and active requests (reservation or rent) 
fact noActiveRequestForDeactivatedUser {
		(no dU : DeactivatedUser | one r : Request | (dU.request = r) and (r.status = ACTIVE))
			// No deactivated users can have an active request
}

// Relation between active requests (reservation or rent) and deactivated users
fact noDeactivatedUserForActiveRequest {
		(all r : Request | r.status = ACTIVE implies 
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

// PaymentStatus DENIED causa Billing Information NOTCONFIRMED - come lo diciamo?


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
fact noDuplicatedRequests {
		(no req1 , req2 : Request | req1.id = req2.id and req1 != req2) and 
		(no res1 , res2 : Reservation | res1.id = res2.id and res1 != res2)  and 
		(no ren1 , ren2 : Rent | ren1.id = ren2.id and ren1 != ren2)
}

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




pred show {}

run show for 1 but exactly 1 User, exactly 1 Request, exactly 1 Car





















