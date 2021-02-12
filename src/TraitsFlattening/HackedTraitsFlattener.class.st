Class {
	#name : #HackedTraitsFlattener,
	#superclass : #Object,
	#instVars : [
		'unchangedClassesAndTraits'
	],
	#category : #'TraitsFlattening-Flattener'
}

{ #category : #private }
HackedTraitsFlattener >> compileMethodsFrom: traitComposition into: aClass [
	(self methodsFrom: traitComposition)
		do: [ :compiledMethod | 
			(aClass selectors includes: compiledMethod selector)
				ifFalse: [ aClass
						compile: compiledMethod sourceCode
						classified: compiledMethod protocol ] ]
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

	self flattenClassesHack: someClasses.
	self restoreChangedClassesIn: someClasses. 
	self restoreUnchangedClasses
]

{ #category : #hack }
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

{ #category : #'when fixed' }
HackedTraitsFlattener >> flattenClassesWhenFixed: someClasses [

	| superclasses subclasses |
	superclasses := OrderedCollection new.
	subclasses := OrderedCollection new.
	someClasses copy do: [ :class | 
		((someClasses includesAny: class allSuperclasses)
			 ifTrue: [ subclasses ]
			 ifFalse: [ superclasses ]) add: class ].
	self privateFlattenClasses: superclasses.
	subclasses ifNotEmpty: [ self flattenClasses: subclasses ]
]

{ #category : #public }
HackedTraitsFlattener >> flattenPackage: aRPackage [
	self flattenClasses: aRPackage classes
]

{ #category : #public }
HackedTraitsFlattener >> flattenPackageNamed: aRPackageName [
	self
		flattenClasses: (RPackage organizer packageNamed: aRPackageName) classes
]

{ #category : #private }
HackedTraitsFlattener >> methodsFrom: traitComposition [
	^ traitComposition selectors removeDuplicates
		collect: [ :sel | traitComposition compiledMethodAt: sel ]
]

{ #category : #private }
HackedTraitsFlattener >> privateFlattenClasses: someClasses [
	someClasses do: [ :class | self flattenClassWhenFixed: class ]
]

{ #category : #hack }
HackedTraitsFlattener >> privateRestoreClasses: someClasses [

	someClasses do: [ :class | 
		self
			restoreClass: class
			withTraitComposition: (self unchangedClassesAndTraits
					 at: class
					 ifAbsent: [ TaEmptyComposition new ]) ]
]

{ #category : #hack }
HackedTraitsFlattener >> restoreChangedClassesIn: someClasses [

	self privateRestoreClasses: (someClasses select: [ :class | 
			 class class class = TraitedMetaclass and: [ 
				 class hasTraitComposition not ] ])
]

{ #category : #hack }
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

{ #category : #hack }
HackedTraitsFlattener >> restoreClasses: someClasses [

	| superclasses |
	superclasses := someClasses reject: [ :class | 
		                someClasses includesAny: class allSuperclasses ].

	self privateRestoreClasses: superclasses.

	(superclasses flatCollect: #allSubclasses) ifNotEmpty: [ :subclasses | 
		self restoreClasses: subclasses ]
]

{ #category : #hack }
HackedTraitsFlattener >> restoreUnchangedClasses [

	self restoreClasses: self unchangedClassesAndTraits keys
]

{ #category : #hack }
HackedTraitsFlattener >> unchangedClassesAndTraits [

	^ unchangedClassesAndTraits ifNil: [ 
		  unchangedClassesAndTraits := Dictionary new ]
]

{ #category : #private }
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
