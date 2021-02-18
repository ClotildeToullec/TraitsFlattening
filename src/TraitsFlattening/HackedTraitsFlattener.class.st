Class {
	#name : #HackedTraitsFlattener,
	#superclass : #Object,
	#instVars : [
		'unchangedClassesAndTraits',
		'traitsAndUsersCache',
		'classesToFlatten',
		'traitsToReinstallOnUsers'
	],
	#category : #'TraitsFlattening-Flattener'
}

{ #category : #private }
HackedTraitsFlattener >> buildTraitsAndUsersCacheFor: someClasses [

	| traits |
	traits := (someClasses flatCollect: #allTraits) asOrderedCollection.
	traitsAndUsersCache := Dictionary
		                       newFromKeys: traits
		                       andValues: (traits collect: [ :trait | 
				                        trait users select: [ :class | 
					                        someClasses includes: class ] ])
]

{ #category : #public }
HackedTraitsFlattener >> changeHierarchyIfNecessaryIn: someClasses [

	| slots traits |
	slots := (someClasses flatCollect: #slots) select: [ :slot | 
		         slot isFMRelationSlot and: [ 
			         slot hasInverse and: [ slot targetClass isTrait ] ] ].
	traits := (slots collect: #targetClass) asOrderedCollection
		          removeDuplicates select: [ :trait | 
		          ((trait users flatCollect: [ :user | 
			            user isTrait
				            ifTrue: [ user users ]
				            ifFalse: [ { user } ] ]) select: [ :class | 
			           someClasses includes: class ]) size > 1 ].
	traitsToReinstallOnUsers := Dictionary
		                            newFromKeys: traits
		                            andValues: (traits collect: #users).
	traits do: [ :trait | self createSuperclassUsing: trait ]
]

{ #category : #public }
HackedTraitsFlattener >> compileMethodsFrom: traitComposition into: aClass [
	(self methodsFrom: traitComposition)
		do: [ :compiledMethod | 
			(aClass selectors includes: compiledMethod selector)
				ifFalse: [ aClass
						compile: compiledMethod sourceCode
						classified: compiledMethod protocol ] ]
]

{ #category : #public }
HackedTraitsFlattener >> createSuperclassUsing: aTrait [

	| subclasses newClassName newClass |
	subclasses := aTrait allUsers flattened select: [ :user | 
		              classesToFlatten includes: user ].
	(subclasses collect: #superclass) asSet size > 1 ifTrue: [ 
		Error signal: 'Impossible to resolve' ].
	newClassName := UIManager default
		                request: (String streamContents: [ :stream | 
				                 stream << 'Choose a name for superclass of:'.
				                 subclasses do: [ :class | 
					                 stream
						                 << ' ';
						                 << class name ] ])
		                initialAnswer: (aTrait name withoutPrefix:
				                 (aTrait name piecesCutWhere: [ :each :next | 
					                  each = $T ]) first) capitalized.
	aTrait users do: [ :user | 
		user removeFromComposition: aTrait.
		user class removeFromComposition: aTrait class ].
	newClass := Smalltalk classInstaller make: [ :aSlotClassBuilder | 
		            aSlotClassBuilder
			            superclass: Object;
			            name: newClassName asSymbol;
			            category: subclasses anyOne category;
			            traitComposition: aTrait ].
	classesToFlatten add: newClass.
	subclasses do: [ :class | class superclass: newClass ]
]

{ #category : #public }
HackedTraitsFlattener >> flattenClass: aClass [

	self flattenClasses: { aClass }
]

{ #category : #public }
HackedTraitsFlattener >> flattenClassWhenFixed: aClass [

	| newClass traitComposition |
	traitComposition := aClass traitComposition.
	newClass := self
		            updateClass: aClass
		            fromTraitComposition: traitComposition.
	self compileMethodsFrom: traitComposition into: aClass.
	self
		compileMethodsFrom: traitComposition classComposition
		into: aClass class.
	^ newClass
]

{ #category : #public }
HackedTraitsFlattener >> flattenClasses: someClasses [

	classesToFlatten := someClasses asOrderedCollection.
	self changeHierarchyIfNecessaryIn: classesToFlatten.
	self buildTraitsAndUsersCacheFor: classesToFlatten.
	self flattenClassesHack: classesToFlatten.
	self restoreChangedClassesIn: classesToFlatten.
	self updateFameSlotsIn: classesToFlatten.
	self restoreUnchangedClasses.
	traitsToReinstallOnUsers keysAndValuesDo: [ :trait :users | 
		users do: [ :user | 
			(user usesTraitLocally: trait) ifFalse: [ 
				user traitComposition: user traitComposition + trait ] ] ]
]

{ #category : #public }
HackedTraitsFlattener >> flattenClassesHack: someClasses [

	| superclasses subclasses unchangedClasses |
	superclasses := OrderedCollection new.
	subclasses := OrderedCollection new.
	someClasses copy do: [ :class | 
		((someClasses includesAny: class allSubclasses)
			 ifTrue: [ superclasses ]
			 ifFalse: [ subclasses ]) add: class ].

	unchangedClasses := (subclasses flatCollect: #allSubclasses) select: [ 
		                    :class | class hasTraitComposition ].
	unchangedClasses do: [ :class | 
		self unchangedClassesAndTraits at: class put: class traitComposition ].

	self privateFlattenClasses: subclasses.
	superclasses ifNotEmpty: [ self flattenClassesHack: superclasses ]
]

{ #category : #public }
HackedTraitsFlattener >> flattenPackage: aRPackage [

	self flattenClasses: aRPackage definedClasses
]

{ #category : #public }
HackedTraitsFlattener >> flattenPackageNamed: aRPackageName [

	self flattenPackage: (RPackage organizer packageNamed: aRPackageName)
]

{ #category : #public }
HackedTraitsFlattener >> methodsFrom: traitComposition [
	^ traitComposition selectors removeDuplicates
		collect: [ :sel | traitComposition compiledMethodAt: sel ]
]

{ #category : #public }
HackedTraitsFlattener >> privateFlattenClasses: someClasses [

	someClasses do: [ :class | self flattenClassWhenFixed: class ].
]

{ #category : #public }
HackedTraitsFlattener >> privateRestoreClasses: someClasses [

	someClasses do: [ :class | 
		self
			restoreClass: class
			withTraitComposition: (self unchangedClassesAndTraits
					 at: class
					 ifAbsent: [ TaEmptyComposition new ]) ]
]

{ #category : #public }
HackedTraitsFlattener >> restoreChangedClassesIn: someClasses [

	self privateRestoreClasses: (someClasses select: [ :class | 
			 class class class = TraitedMetaclass and: [ 
				 class hasTraitComposition not ] ])
]

{ #category : #public }
HackedTraitsFlattener >> restoreClass: aClass withTraitComposition: aTraitComposition [

	^ aClass classInstaller update: aClass to: [ :builder | 
		  builder
			  fillFor: aClass;
			  metaclassClass: (aTraitComposition traits
					   ifEmpty: [ aClass superclass class class ]
					   ifNotEmpty: [ TraitedMetaclass ]);
			  traitComposition: aTraitComposition;
			  classTraitComposition: (aTraitComposition traits collect: #class) ]
]

{ #category : #public }
HackedTraitsFlattener >> restoreClasses: someClasses [

	| superclasses |
	superclasses := someClasses reject: [ :class | 
		                someClasses includesAny: class allSuperclasses ].

	self privateRestoreClasses: superclasses.

	(superclasses flatCollect: #allSubclasses) ifNotEmpty: [ :subclasses | 
		self restoreClasses: subclasses ]
]

{ #category : #public }
HackedTraitsFlattener >> restoreUnchangedClasses [

	self restoreClasses: self unchangedClassesAndTraits keys
]

{ #category : #public }
HackedTraitsFlattener >> unchangedClassesAndTraits [

	^ unchangedClassesAndTraits ifNil: [ 
		  unchangedClassesAndTraits := Dictionary new ]
]

{ #category : #public }
HackedTraitsFlattener >> updateClass: aClass fromTraitComposition: traitComposition [
	^ aClass classInstaller
		update: aClass
		to: [ :builder | 
			builder
				fillFor: aClass;
				metaclassClass: aClass superclass class class;
				traitComposition: {};
				classTraitComposition: {};
				slots: aClass localSlots , traitComposition slots;
				classSlots: aClass class localSlots , traitComposition classComposition slots ]
]

{ #category : #public }
HackedTraitsFlattener >> updateFameSlotsIn: someClasses [

	(someClasses flatCollect: #slots)
		select: [ :slot | 
			slot isFMRelationSlot and: [ 
				slot hasInverse and: [ slot targetClass isTrait ] ] ]
		thenDo: [ :slot | 
			slot inClass: (traitsAndUsersCache
					 at: slot targetClass
					 ifPresent: [ :users | users anyOne ]
					 ifAbsent: [ slot targetClass ]) ]
]
