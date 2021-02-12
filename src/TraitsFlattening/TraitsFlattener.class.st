Class {
	#name : #TraitsFlattener,
	#superclass : #Object,
	#category : #'TraitsFlattening-Flattener'
}

{ #category : #private }
TraitsFlattener >> compileMethodsFrom: traitComposition into: aClass [
	(self methodsFrom: traitComposition)
		do: [ :compiledMethod | 
			(aClass selectors includes: compiledMethod selector)
				ifFalse: [ aClass
						compile: compiledMethod sourceCode
						classified: compiledMethod protocol ] ]
]

{ #category : #public }
TraitsFlattener >> flattenClass: aClass [

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
TraitsFlattener >> flattenClasses: someClasses [

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
TraitsFlattener >> flattenPackage: aRPackage [

	self flattenClasses: aRPackage definedClasses
]

{ #category : #public }
TraitsFlattener >> flattenPackageNamed: aRPackageName [

	self flattenPackage: (RPackage organizer packageNamed: aRPackageName)
]

{ #category : #private }
TraitsFlattener >> methodsFrom: traitComposition [
	^ traitComposition selectors removeDuplicates
		collect: [ :sel | traitComposition compiledMethodAt: sel ]
]

{ #category : #private }
TraitsFlattener >> privateFlattenClasses: someClasses [
	someClasses do: [ :class | self flattenClass: class ]
]

{ #category : #private }
TraitsFlattener >> updateClass: aClass fromTraitComposition: traitComposition [
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
