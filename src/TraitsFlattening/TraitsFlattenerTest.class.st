Class {
	#name : #TraitsFlattenerTest,
	#superclass : #TestCase,
	#instVars : [
		'flattener',
		'trait1',
		'class1',
		'trait2',
		'class2',
		'trait3',
		'class3'
	],
	#category : #'TraitsFlattening-Tests'
}

{ #category : #tests }
TraitsFlattenerTest >> assertTrait: aTrait wasFlattenInto: aClass testingSelector: aSelector [
	self deny: aClass hasTraitComposition.
	self deny: (aTrait users includes: aClass).
	aTrait slotNames
		do: [ :slotName | self assert: (aClass hasSlotNamed: slotName) ].
	self assert: (aClass >> aSelector) isInstalled.
	self assert: (aClass >> aSelector) protocol equals: 'testing'.
	self assert: (aClass new perform: aSelector)
]

{ #category : #classes }
TraitsFlattenerTest >> buildHierarchyOfThreeClassesUsingTraits [
	class1 := self classUsingT1.
	trait2 := self traitNamed: #TraitToFlatten2.
	class2 := self classNamed: #SubclassUsingTrait2 using: trait2.
	trait3 := self traitNamed: #TraitToFlatten3.
	trait3 compile: 'origin ^ ''Trait3''' classified: 'accessing'.
	class3 := self classNamed: #SubclassUsingTrait3 using: trait3.
	class2 superclass: class1.
	class3 superclass: class2
]

{ #category : #classes }
TraitsFlattenerTest >> buildHierarchyOfTwoClassesUsingTraits [
	class1 := self classUsingT1.
	trait2 := self traitNamed: #TraitToFlatten2.
	class2 := self classNamed: #SubclassUsingTrait2 using: trait2.
	class2 superclass: class1
]

{ #category : #traits }
TraitsFlattenerTest >> buildTrait1 [
	trait1 := Trait
		named: #TraitToFlatten1
		uses: {}
		slots: {#slotFromTrait1}
		package: self packageName.
	trait1 compile: 'hasMethodFromTrait1 ^ true' classified: 'testing'.
	trait1
		compile: 'slotFromTrait1 ^ slotFromTrait1'
		classified: 'accessing'.
	trait1
		compile: 'slotFromTrait1: anObject slotFromTrait1 := anObject'
		classified: 'accessing'.
	trait1 compile: 'origin ^ ''Trait1''' classified: 'accessing'.
	trait1 addClassSlot: #classSlotFromT1.
	trait1 classSide
		compile:
			'hasTraitClassMethod
	^ true'
		classified: 'testing'
]

{ #category : #classes }
TraitsFlattenerTest >> classNamed: aClassName using: aTraitComposition [
	^ self
		classNamed: aClassName
		using: aTraitComposition
		slotNames: ''
		classSlotNames: ''
]

{ #category : #classes }
TraitsFlattenerTest >> classNamed: aClassName using: aTraitComposition slotNames: slotNames classSlotNames: classSlotNames [
	^ Object
		subclass: aClassName
		uses: aTraitComposition
		instanceVariableNames: slotNames
		classVariableNames: classSlotNames
		package: self packageName
]

{ #category : #classes }
TraitsFlattenerTest >> classUsing: aTraitComposition [
	^ self
		classNamed: #ClassUsingTraitComposition
		using: aTraitComposition
]

{ #category : #classes }
TraitsFlattenerTest >> classUsingT1 [
	^ self classNamed: #ClassUsingTrait1 using: trait1
]

{ #category : #classes }
TraitsFlattenerTest >> classUsingT1WithLocalSlotsAndMethods [
	| newClass |
	newClass := self
		classNamed: #ClassWithSlotsAndMethods
		using: trait1
		slotNames: 'slotFromC1'
		classSlotNames: 'classSlotFromT1'.
	newClass compile: 'hasLocalMethodFromC1 ^true' classified: 'local'.
	newClass class
		compile: 'hasClassLocalMethodFromC1 ^true'
		classified: 'class-local'.
	^ newClass
]

{ #category : #traits }
TraitsFlattenerTest >> defaultSecondSlotName [
	^ #slotFromTrait2
]

{ #category : #running }
TraitsFlattenerTest >> packageName [
	^ 'TraitsFlattening-Tests'
]

{ #category : #running }
TraitsFlattenerTest >> setUp [
	super setUp.
	flattener := TraitsFlattener new.
	self buildTrait1
]

{ #category : #running }
TraitsFlattenerTest >> tearDown [
	{class1.
	class2.
	class3.
	trait1.
	trait2.
	trait3}
		do:
			[ :classOrTrait | classOrTrait ifNotNil: [ classOrTrait removeFromSystem ] ].
	super tearDown
]

{ #category : #tests }
TraitsFlattenerTest >> testClassMetaClass [
	class1 := self classUsingT1.
	flattener flattenClass: class1.
	self assert: class1 class class equals: Metaclass
]

{ #category : #tests }
TraitsFlattenerTest >> testClassSide [
	class1 := self classUsingT1.
	flattener flattenClass: class1.
	self deny: class1 class hasTraitComposition.
	self deny: (trait1 class users includes: class1 class).
	self assert: (class1 class hasSlotNamed: #classSlotFromT1).
	self assert: (class1 class >> #hasTraitClassMethod) isInstalled.
	self
		assert: (class1 class >> #hasTraitClassMethod) protocol
		equals: 'testing'.
	self assert: (class1 perform: #hasTraitClassMethod)
]

{ #category : #tests }
TraitsFlattenerTest >> testDoNotflattenMiddleClass [
	| origin1 origin2 origin3 |
	self buildHierarchyOfThreeClassesUsingTraits.
	origin1 := class1 new origin.
	origin2 := class2 new origin.
	origin3 := class3 new origin.

	flattener flattenClasses: {class1. class3}.

	self assert: class1 new origin equals: origin1.
	self assert: class2 new origin equals: origin2.
	self assert: class3 new origin equals: origin3.
	self assert: class1 class class equals: Metaclass.
	self assert: class2 class class equals: TraitedMetaclass.
	self assert: class2 class class equals: TraitedMetaclass
]

{ #category : #tests }
TraitsFlattenerTest >> testFlattenOnlySubclass [
	| origin1 origin2 |
	self buildHierarchyOfTwoClassesUsingTraits.
	origin1 := class1 new origin.
	origin2 := class2 new origin.

	flattener flattenClass: class2.

	self assert: class1 new origin equals: origin1.
	self assert: class2 new origin equals: origin2.
	self assert: class1 hasTraitComposition.
	self assert: (trait1 users includes: class1).
	self deny: class2 hasTraitComposition.
	self deny: (trait2 users includes: class2).
	{class1.
	class2}
		do: [ :class | self assert: class class class equals: TraitedMetaclass ]
]

{ #category : #tests }
TraitsFlattenerTest >> testFlattenOnlySuperclass [
	| origin1 origin2 |
	self buildHierarchyOfTwoClassesUsingTraits.
	origin1 := class1 new origin.
	origin2 := class2 new origin.

	flattener flattenClass: class1.

	self assert: class1 new origin equals: origin1.
	self assert: class2 new origin equals: origin2.
	self deny: class1 hasTraitComposition.
	self deny: (trait1 users includes: class1).
	self assert: class2 hasTraitComposition.
	self assert: (trait2 users includes: class2).
	self assert: class1 class class equals: Metaclass.
	self assert: class2 class class equals: TraitedMetaclass
]

{ #category : #tests }
TraitsFlattenerTest >> testHierarchy [
	| origin1 origin2 |
	self buildHierarchyOfTwoClassesUsingTraits.
	origin1 := class1 new origin.
	origin2 := class2 new origin.
	flattener
		flattenClasses:
			{class1.
			class2}.
	self assert: class1 new origin equals: origin1.
	self assert: class2 new origin equals: origin2.
	{class1.
	class2}
		do: [ :class | self assert: class class class equals: Metaclass ]
]

{ #category : #tests }
TraitsFlattenerTest >> testHierarchyFlatteningOrder [
	| origin1 origin2 |
	self buildHierarchyOfTwoClassesUsingTraits.
	origin1 := class1 new origin.
	origin2 := class2 new origin.

	"Class before superclass"
	flattener
		flattenClasses:
			{class2.
			class1}.
	self assert: class1 new origin equals: origin1.
	self assert: class2 new origin equals: origin2.
	{class1.
	class2}
		do: [ :class | self assert: class class class equals: Metaclass ]
]

{ #category : #tests }
TraitsFlattenerTest >> testInstanceSideAccessors [
	| instance |
	class1 := self classUsingT1.
	flattener flattenClass: class1.
	self deny: class1 hasTraitComposition.
	self assertEmpty: trait1 users.
	instance := class1 new.
	self
		shouldnt: [ instance perform: #slotFromTrait1: with: true ]
		raise: MessageNotUnderstood.
	self
		shouldnt: [ instance perform: #slotFromTrait1 ]
		raise: MessageNotUnderstood.
	self assert: (instance perform: #slotFromTrait1)
]

{ #category : #tests }
TraitsFlattenerTest >> testInstanceSideMethod [
	class1 := self classUsingT1.
	flattener flattenClass: class1.
	self assert: (class1 >> #hasMethodFromTrait1) isInstalled.
	self
		assert: (class1 >> #hasMethodFromTrait1) protocol
		equals: 'testing'.
	self assert: (class1 new perform: #hasMethodFromTrait1)
]

{ #category : #tests }
TraitsFlattenerTest >> testInstanceSideSlot [
	class1 := self classUsingT1.
	flattener flattenClass: class1.
	self assert: (class1 hasSlotNamed: #slotFromTrait1)
]

{ #category : #tests }
TraitsFlattenerTest >> testKeepLocalSlotsAndMethods [
	class1 := self classUsingT1WithLocalSlotsAndMethods.
	flattener flattenClass: class1.

	"Instace side"
	self assert: (class1 hasSlotNamed: 'slotFromC1').
	self assert: (class1 >> #hasLocalMethodFromC1) isInstalled.
	self
		assert: (class1 >> #hasLocalMethodFromC1) protocol
		equals: 'local'.
	self assert: (class1 new perform: #hasLocalMethodFromC1).

	"Class side"
	self assert: (class1 class hasSlotNamed: 'classSlotFromT1').
	self assert: (class1 class >> #hasClassLocalMethodFromC1) isInstalled.
	self
		assert: (class1 class >> #hasClassLocalMethodFromC1) protocol
		equals: 'class-local'.
	self assert: (class1 perform: #hasClassLocalMethodFromC1)
]

{ #category : #tests }
TraitsFlattenerTest >> testLocalPrecedence [
	class1 := self classUsingT1.
	class1 compile: 'origin ^ ''Class1''' classified: 'accessing'.
	flattener flattenClass: class1.
	self
		assertTrait: trait1
		wasFlattenInto: class1
		testingSelector: #hasMethodFromTrait1.
	self assert: (class1 >> #origin) isInstalled.
	self assert: (class1 >> #origin) protocol equals: 'accessing'.
	self assert: (class1 new perform: #origin) equals: 'Class1'
]

{ #category : #tests }
TraitsFlattenerTest >> testOthersUsersUnchanged [
	class1 := self classUsingT1.
	class2 := self
		classNamed: #OtherClassUsingTraitComposition
		using: trait1.
	flattener flattenClass: class1.
	self deny: (trait1 users includes: class1).
	self assert: (trait1 users includes: class2).
	self deny: class1 hasTraitComposition.
	self assert: class2 traits anyOne equals: trait1
]

{ #category : #tests }
TraitsFlattenerTest >> testOverridenMethod [
	| expectedOrigin |
	class1 := self classNamed: #SuperClassForClass1 using: {}.
	class1 compile: 'origin ^ ''Superclass'' ' classified: 'accessing'.

	class2 := self classUsingT1.
	class2 superclass: class1.

	expectedOrigin := class2 new origin.

	flattener flattenClass: class2.

	self assert: class2 new origin equals: expectedOrigin
]

{ #category : #tests }
TraitsFlattenerTest >> testRemoveFromUsers [
	class1 := self classUsingT1.
	flattener flattenClass: class1.
	self deny: (trait1 users includes: class1)
]

{ #category : #tests }
TraitsFlattenerTest >> testRemoveTraitComposition [
	class1 := self classUsingT1.
	flattener flattenClass: class1.
	self deny: class1 hasTraitComposition
]

{ #category : #tests }
TraitsFlattenerTest >> testTraitComposition [
	trait2 := self traitNamed: #TraitToFlatten2.
	class1 := self classUsing: trait1 + trait2.
	flattener flattenClass: class1.
	self
		assertTrait: trait1
		wasFlattenInto: class1
		testingSelector: #hasMethodFromTrait1.
	self
		assertTrait: trait2
		wasFlattenInto: class1
		testingSelector: #hasMethodFromTrait2
]

{ #category : #tests }
TraitsFlattenerTest >> testTraitPrecedence [
	trait2 := self traitWithPrecedence.
	class1 := self classUsing: (trait1 + trait2 withPrecedenceOf: trait2).
	flattener flattenClass: class1.
	self
		assertTrait: trait1
		wasFlattenInto: class1
		testingSelector: #hasMethodFromTrait1.
	self
		assertTrait: trait2
		wasFlattenInto: class1
		testingSelector: #hasMethodFromTrait2.
	self assert: (class1 >> #origin) isInstalled.
	self assert: (class1 >> #origin) protocol equals: 'accessing'.
	self
		assert: (class1 new perform: #origin)
		equals: 'TraitWithPrecedence'
]

{ #category : #tests }
TraitsFlattenerTest >> testTraitUsingTrait [
	trait2 := self traitNamed: #TUsingATrait using: trait1.
	class1 := self classUsing: trait2.
	flattener flattenClass: class1.
	self assertCollection: trait1 users hasSameElements: {trait2}.
	self assertCollection: trait2 traits hasSameElements: {trait1}.
	self
		assertTrait: trait1
		wasFlattenInto: class1
		testingSelector: #hasMethodFromTrait1.
	self
		assertTrait: trait2
		wasFlattenInto: class1
		testingSelector: #hasMethodFromTrait2
]

{ #category : #traits }
TraitsFlattenerTest >> traitNamed: aTraitName [
	^ self traitNamed: aTraitName using: {} slots: {}
]

{ #category : #traits }
TraitsFlattenerTest >> traitNamed: aTraitName using: aTraitComposition [
	^ self traitNamed: aTraitName using: aTraitComposition slots: {}
]

{ #category : #traits }
TraitsFlattenerTest >> traitNamed: aTraitName using: aTraitComposition slots: slots [
	| trait |
	trait := Trait
		named: aTraitName
		uses: aTraitComposition
		slots: slots , {self defaultSecondSlotName}
		package: self packageName.
	trait compile: 'hasMethodFromTrait2 ^ true' classified: 'testing'.
	trait compile: 'origin ^ ''Trait2''' classified: 'accessing'.
	^ trait
]

{ #category : #traits }
TraitsFlattenerTest >> traitWithClassSideMethod [
	| trait |
	trait := self traitNamed: #TWithClassMethod.
	trait classSide
		compile:
			'hasTraitClassMethod
	^ true'
		classified: 'testing'.
	^ trait
]

{ #category : #traits }
TraitsFlattenerTest >> traitWithPrecedence [
	| trait |
	trait := self traitNamed: #TWithPrecedence.
	trait
		compile: 'origin ^ ''TraitWithPrecedence'''
		classified: 'accessing'.
	^ trait
]
