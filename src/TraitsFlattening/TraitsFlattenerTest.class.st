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
TraitsFlattenerTest >> assertClass: aClass stillUsesTrait: aTrait [

	self assert: (aClass traits includes: aTrait).
	self assert: (aTrait users includes: aClass).
	self assert: aClass class class equals: TraitedMetaclass
]

{ #category : #tests }
TraitsFlattenerTest >> assertTrait: aTrait wasFlattenInto: aClass [

	| selector |
	self deny: aClass hasTraitComposition.
	self deny: (aTrait allUsers includes: aClass).

	aTrait slotNames do: [ :slotName | 
		self assert: (aClass hasSlotNamed: slotName) ].

	selector := self testingSelectorFromTrait: aTrait.
	self assert: (aClass >> selector) isInstalled.
	self
		assert: (aClass >> selector) protocol
		equals: (aTrait >> selector) protocol.
	self assert: (aClass new perform: selector).

	self assert: aClass class class equals: aClass superclass class class
]

{ #category : #classes }
TraitsFlattenerTest >> buildClass1 [

	class1 := Object
		          subclass: #Class1UsingTrait1
		          uses: trait1
		          instanceVariableNames: self class1SlotName
		          classVariableNames: ''
		          package: self packageName.
	class1 class instanceVariableNames: self class1ClassSlotName.
	class1
		compile: self class1LocalSelector asString , ' ^true'
		classified: 'local'.
	class1 class
		compile: self class1LocalClassSelector asString , ' ^true'
		classified: 'class-local'
]

{ #category : #classes }
TraitsFlattenerTest >> buildClassesHierarchy [

	class2 := self secondClassUsing: trait2 superclass: class1.
	class3 := self thirdClassUsing: trait3 superclass: class2
]

{ #category : #traits }
TraitsFlattenerTest >> buildTrait1 [

	trait1 := Trait
		          named: #TraitToFlatten1
		          uses: {  }
		          slots: { self trait1SlotName }
		          package: self packageName.

	"Instance side methods"
	trait1 compile: 'hasMethodFromTrait1 ^ true' classified: 'testing'.
	trait1 compile: 'origin ^ ''Trait1''' classified: 'accessing'.

	"Accessors"
	trait1
		compile: self trait1SlotName asString , ' ^ slotFromTrait1'
		classified: 'accessing'.
	trait1
		compile: self trait1SlotName asMutator asString
			, ' anObject slotFromTrait1 := anObject'
		classified: 'accessing'.

	"Class side"
	trait1 addClassSlot: self trait1ClassSlotName.
	trait1 classSide
		compile: self trait1ClassSideSelector , '
	^ true'
		classified: 'testing'
]

{ #category : #traits }
TraitsFlattenerTest >> buildTrait2 [

	trait2 := self secondTraitUsing: {  }
]

{ #category : #traits }
TraitsFlattenerTest >> buildTrait3 [

	trait3 := self thirdTraitUsing: {  }
]

{ #category : #accessing }
TraitsFlattenerTest >> class1 [

	^ class1
]

{ #category : #literals }
TraitsFlattenerTest >> class1ClassSlotName [

	^ 'classSlotFromClass1'
]

{ #category : #literals }
TraitsFlattenerTest >> class1LocalClassSelector [

	^ #hasLocalClassMethod
]

{ #category : #literals }
TraitsFlattenerTest >> class1LocalSelector [

	^ #hasLocalMethod
]

{ #category : #literals }
TraitsFlattenerTest >> class1SlotName [

	^ 'slotFromClass1'
]

{ #category : #classes }
TraitsFlattenerTest >> classes [

	^ { 
		  class1.
		  class2.
		  class3 } reject: #isNil
]

{ #category : #literals }
TraitsFlattenerTest >> packageName [

	^ 'TraitsFlattening-TestExamples'
]

{ #category : #classes }
TraitsFlattenerTest >> secondClassUsing: aTraitComposition [

	^ self secondClassUsing: aTraitComposition superclass: Object
]

{ #category : #classes }
TraitsFlattenerTest >> secondClassUsing: aTraitComposition superclass: aSuperclass [

	^ aSuperclass
		  subclass: #Class2InFlatteningTests
		  uses: aTraitComposition
		  instanceVariableNames: 'slotFromClass2'
		  classVariableNames: 'classSlotFromClass2'
		  package: self packageName
]

{ #category : #traits }
TraitsFlattenerTest >> secondTraitUsing: aTraitComposition [

	| trait |
	trait := Trait
		         named: #TraitToFlatten2
		         uses: aTraitComposition
		         slots: { #slotFromTrait2 }
		         package: self packageName.
	trait compile: 'hasMethodFromTrait2 ^ true' classified: 'testing'.
	trait compile: 'origin ^ ''Trait2''' classified: 'accessing'.
	^ trait
]

{ #category : #running }
TraitsFlattenerTest >> setUp [

	super setUp.
	EpMonitor current disable.
	flattener := HackedTraitsFlattener new.
	self buildTrait1.
	self buildClass1.
	self buildTrait2.
	self buildTrait3
]

{ #category : #running }
TraitsFlattenerTest >> tearDown [

	"	{ 
		class1.
		class2.
		class3.
		trait1.
		trait2.
		trait3 } do: [ :classOrTrait | 
		classOrTrait ifNotNil: [ classOrTrait removeFromSystem ] ]."

	((RPackage organizer packageNamed: 'TraitsFlattening') 
		 classTagNamed: 'TestExamples') classes do: #removeFromSystem.
	EpMonitor current enable.
	super tearDown
]

{ #category : #tests }
TraitsFlattenerTest >> testClassMetaClass [

	flattener flattenClass: class1.

	self assert: class1 class class equals: Metaclass
]

{ #category : #tests }
TraitsFlattenerTest >> testClassSide [

	flattener flattenClass: class1.

	self deny: class1 class hasTraitComposition.
	self deny: (trait1 class users includes: class1 class).

	self assert: (class1 class hasSlotNamed: self trait1ClassSlotName).

	self assert:
		(class1 class >> self trait1ClassSideSelector) isInstalled.
	self
		assert: (class1 class >> self trait1ClassSideSelector) protocol
		equals: (trait1 class >> self trait1ClassSideSelector) protocol.
	self assert: (class1 perform: self trait1ClassSideSelector)
]

{ #category : #tests }
TraitsFlattenerTest >> testDoNotflattenMiddleClass [

	| origin1 origin2 origin3 |
	self buildClassesHierarchy.

	origin1 := class1 new origin.
	origin2 := class2 new origin.
	origin3 := class3 new origin.

	flattener flattenClasses: { 
			class1.
			class3 }.

	self assert: class1 new origin equals: origin1.
	self assert: class2 new origin equals: origin2.
	self assert: class3 new origin equals: origin3.

	self assertTrait: trait1 wasFlattenInto: class1.
	self assertClass: class2 stillUsesTrait: trait2.
	self assertTrait: trait3 wasFlattenInto: class3
]

{ #category : #tests }
TraitsFlattenerTest >> testFMSlots [

	| slot1 slot2 |
	trait1 addSlot: (#fmSlot => FMOne type: trait2 opposite: #fmOpposite).
	trait2 addSlot: (#fmOpposite => FMOne type: trait1 opposite: #fmSlot).
	class2 := self secondClassUsing: trait2.
	flattener flattenClasses: self classes.
	slot1 := class1 slotNamed: #fmSlot.
	slot2 := class2 slotNamed: #fmOpposite.
	self assert: slot1 hasInverse.
	self assert: slot1 definingClass equals: class1.
	self assert: slot1 targetClass equals: class2.

	self assert: slot2 hasInverse.
	self assert: slot2 definingClass equals: class2.
	self assert: slot2 targetClass equals: class1
]

{ #category : #tests }
TraitsFlattenerTest >> testFMSlotsWithSeveralUsers [

	| slot1 slot2 slot3 newClass |
	self buildTrait2.
	trait1 addSlot: (#fmSlot => FMOne type: trait2 opposite: #fmOpposite).
	trait2 addSlot: (#fmOpposite => FMOne type: trait1 opposite: #fmSlot).

	class2 := self secondClassUsing:
		          (Trait
			           named: #TraitToFlatten3
			           uses: trait2
			           package: self packageName).
	class3 := self thirdClassUsing:
		          (Trait
			           named: #TraitToFlatten4
			           uses: trait2
			           package: self packageName).

"	UIManager nonInteractiveDuring: [ 
		[ "flattener flattenClasses: self classes "]
			on: ProvideAnswerNotification
			do: [ :e | e resume: #NewSuperclassToFlatten ] ]".
	slot1 := class1 slotNamed: #fmSlot.
	slot2 := class2 slotNamed: #fmOpposite.
	slot3 := class3 slotNamed: #fmOpposite.

	newClass := class2 commonSuperclassWith: class3.
	self deny: newClass identicalTo: Object.
	self assertTrait: trait2 wasFlattenInto: newClass.

	self assert: slot1 hasInverse.
	self assert: slot1 definingClass equals: class1.
	self assert: slot1 targetClass equals: newClass.
	self assert: slot2 hasInverse.
	self assert: slot2 definingClass equals: newClass.
	self assert: slot2 targetClass equals: class1.
	self assert: slot3 hasInverse.
	self assert: slot3 definingClass equals: newClass.
	self assert: slot3 targetClass equals: class1
]

{ #category : #tests }
TraitsFlattenerTest >> testFlattenAllHierarchy [

	| origin1 origin2 origin3 |
	self buildClassesHierarchy.

	origin1 := class1 new origin.
	origin2 := class2 new origin.
	origin3 := class3 new origin.

	flattener flattenClasses: self classes.

	self assert: class1 new origin equals: origin1.
	self assert: class2 new origin equals: origin2.
	self assert: class3 new origin equals: origin3.

	self classes
		with: self traits
		do: [ :class :trait | self assertTrait: trait wasFlattenInto: class ]
]

{ #category : #tests }
TraitsFlattenerTest >> testFlattenAllTraitsInComposition [

	class1 setTraitComposition: trait1 + trait2.
	
	flattener flattenClass: class1.
	
	self assertTrait: trait1 wasFlattenInto: class1.
	self assertTrait: trait2 wasFlattenInto: class1
]

{ #category : #tests }
TraitsFlattenerTest >> testFlattenOnlySubclass [

	| origin1 origin2 |
	self buildClassesHierarchy.

	origin1 := class1 new origin.
	origin2 := class2 new origin.

	flattener flattenClass: class2.

	self assert: class1 new origin equals: origin1.
	self assert: class2 new origin equals: origin2.

	self assertClass: class1 stillUsesTrait: trait1.
	self assertTrait: trait2 wasFlattenInto: class2
]

{ #category : #tests }
TraitsFlattenerTest >> testFlattenOnlySuperclass [

	| origin1 origin2 |
	self buildClassesHierarchy.

	origin1 := class1 new origin.
	origin2 := class2 new origin.

	flattener flattenClass: class1.

	self assert: class1 new origin equals: origin1.
	self assert: class2 new origin equals: origin2.

	self assertTrait: trait1 wasFlattenInto: class1.
	self assertClass: class2 stillUsesTrait: trait2
]

{ #category : #tests }
TraitsFlattenerTest >> testFlatteningRespectsTraitsPrecedence [

	class1 setTraitComposition:
		(trait1 + trait2 withPrecedenceOf: trait2).
	flattener flattenClass: class1.

	self assertTrait: trait1 wasFlattenInto: class1.
	self assertTrait: trait2 wasFlattenInto: class1.

	self assert: (class1 new perform: #origin) equals: 'Trait2'
]

{ #category : #tests }
TraitsFlattenerTest >> testHierarchyFlatteningOrder [

	| origin1 origin2 origin3 |
	self buildClassesHierarchy.

	origin1 := class1 new origin.
	origin2 := class2 new origin.
	origin3 := class3 new origin.

	flattener flattenClasses: self classes shuffle.

	self assert: class1 new origin equals: origin1.
	self assert: class2 new origin equals: origin2.
	self assert: class3 new origin equals: origin3.

	self classes
		with: self traits
		do: [ :class :trait | self assertTrait: trait wasFlattenInto: class ]
]

{ #category : #tests }
TraitsFlattenerTest >> testInstanceSideAccessors [

	| instance |
	flattener flattenClass: class1.

	instance := class1 new.

	self
		shouldnt: [ 
		instance perform: self trait1SlotName asMutator with: true ]
		raise: MessageNotUnderstood.
	self
		shouldnt: [ instance perform: self trait1SlotName ]
		raise: MessageNotUnderstood.
	self assert: (instance perform: self trait1SlotName)
]

{ #category : #tests }
TraitsFlattenerTest >> testInstanceSideMethod [

	| selector |
	selector := self testingSelectorFromTrait: trait1.

	flattener flattenClass: class1.

	self assert: (class1 >> selector) isInstalled.
	self
		assert: (class1 >> selector) protocol
		equals: (trait1 >> selector) protocol.
	self assert: (class1 new perform: selector)
]

{ #category : #tests }
TraitsFlattenerTest >> testInstanceSideSlot [

	flattener flattenClass: class1.

	self assert: (class1 hasSlotNamed: self trait1SlotName).
	self
		assert: (class1 slotNamed: self trait1SlotName) definingClass
		equals: class1
]

{ #category : #tests }
TraitsFlattenerTest >> testKeepLocalSlotsAndMethods [

	flattener flattenClass: class1.

	"Instace side"
	self assert: (class1 hasSlotNamed: self class1SlotName).
	self assert: (class1 >> self class1LocalSelector) isInstalled.
	self
		assert: (class1 >> self class1LocalSelector) protocol
		equals: 'local'.
	self assert: (class1 new perform: self class1LocalSelector).

	"Class side"
	self assert: (class1 class hasSlotNamed: self class1ClassSlotName).
	self assert:
		(class1 class >> self class1LocalClassSelector) isInstalled.
	self
		assert: (class1 class >> self class1LocalClassSelector) protocol
		equals: 'class-local'.
	self assert: (class1 perform: self class1LocalClassSelector)
]

{ #category : #tests }
TraitsFlattenerTest >> testOthersUsersUnchanged [

	class2 := self secondClassUsing: trait1.

	flattener flattenClass: class1.

	self assertTrait: trait1 wasFlattenInto: class1.
	self assertClass: class2 stillUsesTrait: trait1
]

{ #category : #tests }
TraitsFlattenerTest >> testPrecedenceOfLocalMethodOverTrait [

	class1 compile: 'origin ^ ''Class1''' classified: 'accessing'.

	flattener flattenClass: class1.

	self assertTrait: trait1 wasFlattenInto: class1.

	self assert: class1 new origin equals: 'Class1'
]

{ #category : #tests }
TraitsFlattenerTest >> testPrecedenceOfTraitOverSuperclass [

	class1 compile: 'origin ^ ''Class1'' ' classified: 'accessing'.

	self buildClassesHierarchy.

	flattener flattenClass: class2.

	self assert: class2 new origin equals: 'Trait2'
]

{ #category : #tests }
TraitsFlattenerTest >> testPrecedenceOfTraitOverTheTraitItUses [

	trait2 := self secondTraitUsing: trait1.

	class2 := self secondClassUsing: trait2.

	flattener flattenClass: class2.

	self assert: class2 new origin equals: 'Trait2'
]

{ #category : #tests }
TraitsFlattenerTest >> testRemoveFromUsers [

	flattener flattenClass: class1.
	
	self deny: (trait1 allUsers includes: class1)
]

{ #category : #tests }
TraitsFlattenerTest >> testRemoveTraitComposition [

	flattener flattenClass: class1.
	
	self deny: class1 hasTraitComposition
]

{ #category : #tests }
TraitsFlattenerTest >> testTraitUsingTrait [

	trait2 := self secondTraitUsing: trait1.

	class2 := self secondClassUsing: trait2.

	flattener flattenClass: class2.

	self assertCollection: trait1 users hasSameElements: { 
			trait2.
			class1 }.
	self assertCollection: trait2 traits hasSameElements: { trait1 }.

	self assertTrait: trait1 wasFlattenInto: class2.
	self assertTrait: trait2 wasFlattenInto: class2
]

{ #category : #traits }
TraitsFlattenerTest >> testingSelectorFromTrait: aTrait [

	^ #hasMethodFromTrait , (self traits indexOf: aTrait) asString
]

{ #category : #classes }
TraitsFlattenerTest >> thirdClassUsing: aTraitComposition [

	^ self thirdClassUsing: aTraitComposition superclass: Object
]

{ #category : #classes }
TraitsFlattenerTest >> thirdClassUsing: aTraitComposition superclass: aSuperclass [

	^ aSuperclass
		  subclass: #Class3InFlatteningTests
		  uses: aTraitComposition
		  instanceVariableNames: 'slotFromClass3'
		  classVariableNames: 'classSlotFromClass3'
		  package: self packageName
]

{ #category : #traits }
TraitsFlattenerTest >> thirdTraitUsing: aTraitComposition [

	| trait |
	trait := Trait
		         named: #TraitToFlatten3
		         uses: aTraitComposition
		         slots: { #slotFromTrait3 }
		         package: self packageName.
	trait compile: 'hasMethodFromTrait3 ^ true' classified: 'testing'.
	trait compile: 'origin ^ ''Trait3''' classified: 'accessing'.
	^ trait
]

{ #category : #accessing }
TraitsFlattenerTest >> trait1 [

	^ trait1
]

{ #category : #literals }
TraitsFlattenerTest >> trait1ClassSideSelector [

	^ #hasTraitClassMethod
]

{ #category : #literals }
TraitsFlattenerTest >> trait1ClassSlotName [

	^ #classSlotFromT1
]

{ #category : #literals }
TraitsFlattenerTest >> trait1SlotName [

	^ #slotFromTrait1
]

{ #category : #accessing }
TraitsFlattenerTest >> trait2 [

	^ trait2
]

{ #category : #traits }
TraitsFlattenerTest >> traits [

	^ { 
		  trait1.
		  trait2.
		  trait3 }
]
