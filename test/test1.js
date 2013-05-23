require('../index');
var test = require('tape')

var sentences = [
	"Mr. Green killed Colonel Mustard in the study with the candlestick. Mr. Green is not a very nice fellow.",
	"Professor Plumb has a green plant in his study.",
	"Miss Scarlett watered Professor Plumb's green plant while he was away from his office last week."
]

var allCount = { corpu: 1,
     green: 4,
     kill: 1,
     colonel: 1,
     mustard: 1,
     studi: 2,
     candlestick: 1,
     veri: 1,
     nice: 1,
     fellow: 1,
     professor: 2,
     plumb: 2,
     plant: 2,
     miss: 1,
     scarlett: 1,
     water: 1,
     awai: 1,
     offic: 1,
     last: 1,
     week: 1 }
, tfidf = { green: 0.3647817481888638,
   kill: 0.23010299956639813,
   colonel: 0.23010299956639813,
   mustard: 0.23010299956639813,
   studi: 0.2,
   candlestick: 0.23010299956639813,
   veri: 0.23010299956639813,
   nice: 0.23010299956639813,
   fellow: 0.23010299956639813 }
, occurrences = { green: 3,
   kill: 1,
   colonel: 1,
   mustard: 1,
   studi: 2,
   candlestick: 1,
   veri: 1,
   nice: 1,
   fellow: 1,
   professor: 2,
   plumb: 2,
   plant: 2,
   miss: 1,
   scarlett: 1,
   water: 1,
   awai: 1,
   offic: 1,
   last: 1,
   week: 1 }
, doclist = { green: 2,
  kill: 1,
  colonel: 1,
  mustard: 1,
  studi: 1,
  candlestick: 1,
  veri: 1,
  nice: 1,
  fellow: 1 };

test('js-text', function(t) {
	var sample = _.process(sentences);

	t.plan(9);
	
	// math library test
	t.equal(_.sum([1,2,3]) + _.pow(2,3) + _.sqrt(81) + _.div(21,3) + _.log10(10000), (6+8+9+7+4), 'math-library-test')
	
	// computing tfidf values tests
	t.equal(_.isEqual(sample.doclist[0].values, doclist), true, 'doclist');
	t.equal(_.isEqual(sample.occurrences.values, occurrences), true, 'occcurrences');
	t.equal(_.isEqual(sample.tfidf[0].values, tfidf), true, 'tfidf');
	t.equal(_.isEqual(sample.counts.values, allCount), true, 'count');
	
	// try searching against the set of sentences
	t.equal(_.identical(_.flatten(sample.search('green plant mustard fellow')), 
				[ 0, 0.82498774732166, 1, 0.7647817481888638, 2, 0.34762806735857443 ]), 
				true, 'first-text');
	
	t.equal(_.identical(_.flatten(sample.search('green plant plumb')), 			
				[ 1, 1.1647817481888638, 2, 0.5294462491767562, 0, 0.3647817481888638 ]), 
				true, 'second-text');
				
	t.equal(_.identical(_.flatten(sample.search('green study')), 
				[ 1, 0.7647817481888638, 0, 0.5647817481888637, 2, 0.1658098855403926 ]), 
				true, 'third-text');
				
	t.equal(_.flatten(sample.sort(sample.search('green study'))).join(''), 			
		[ 	'Professor Plumb has a green plant in his study.',
			'Mr. Green killed Colonel Mustard in the study with the candlestick. Mr. Green is not a very nice fellow.',
			'Miss Scarlett watered Professor Plumb\'s green plant while he was away from his office last week.' ].join(''), 'fourth-text');
	
});