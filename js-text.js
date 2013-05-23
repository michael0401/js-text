/* ===================================================
 * js-text.js v0.01
 * https://github.com/rranauro/boxspringjs
 * ===================================================
 * Copyright 2013 Incite Advisors, Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 * ========================================================== */

if (typeof _ === 'undefined') {
	if (typeof exports !== 'undefined') {
		var _ = require('underscore');
	} else {
		throw new Error('js-text depends on Underscore.js');
	}
}

var stemmer = require('porter-stemmer').stemmer;
var hash = require('js-hash');

(function() {
	"use strict";
	var JSTEXT= {}
	
	// sums the elements of an array
	var sum = function (a) {

		if (a.length === 0) {
			return 0;
		}
		return (_.reduce(a, function(memo, num){ return memo + num; }, 0));
	};
	JSTEXT.sum = sum;

	var pow = function (x, pwr) {

		return Math.pow(x, pwr);
	};
	JSTEXT.pow = pow;

	var sumSq = function (vector) {			
		if (vector.length === 0) {
			return 0;
		}

		return ( sum(_.map(vector, function(item) {
			return pow(item, 2);
		})));
	};
	JSTEXT.sumSq = sumSq;

	var sqrt = function (x) {
		if (typeof x !== 'number') {
			throw 'error: argument or object of square root must be a number - ' + typeof x;
		}

		return Math.sqrt(x);
	};
	JSTEXT.sqrt = sqrt;

	var div = function (num, den) {			
		if (den === 0) {
			return 0;
		} 
		return (num / den);
	};
	JSTEXT.div = div;

	var log10 = function (val) {
		return Math.log(val) / Math.log(10);
	};
	JSTEXT.log10 = log10;

	var computeTfidf = function (count, words_in_doc, total_docs, docs_with_term) {
		var idf = function (num_docs, docs_with_term) { 
			try {
				return(1.0 + (log10(num_docs / docs_with_term)));
			}
			catch (e) {
				return 1.0;
			}
		};
		//console.log(count, words_in_doc, total_docs, docs_with_term, idf(total_docs, docs_with_term));			
		return((count / words_in_doc)*idf(total_docs, docs_with_term));	
	};
	JSTEXT.computeTfidf = computeTfidf;

	var dotProduct = function(v1, v2) {
		var intersection = _.intersection(_.keys(v1), _.keys(v2));
			
		return (_.reduce(_.map(intersection, 
		// map
		function(item) {
			return (v1[item] * v2[item]);
		}), 
		// reduce
		function(result, product) { 
			return result + product; 
		}, 0));
	};
	JSTEXT.dotProduct = dotProduct;

	// Purpose: Methods for scoring similarity of documents and clustering them.		
	var similarity = function () {
		var cluster = {};

		// setter/getter. returns and object { left: itemI, right: itemJ }
		var best = function () {
			var best_score, left, right, that = {}, intersects;

			var score = function (l, r, score, X) {
				if (l && r) {
					if (typeof best_score === 'undefined' || score > best_score) {
						best_score = score;
						left = l;
						right = r;
						intersects = X || {};
					}						
				}
				return {
					'left': left,
					'right': right,
					'score': best_score,
					'intersects': intersects
				};				
			};
			that.score = score;
			return that;
		};
		cluster.best = best;

		// v1, v2 are objects { 'word':tfidf, ...} { ... }
		var euclid = function (v1, v2) {				
			// Nothing to correlate
			if (_.isEmpty(v1)) {
				return 0;
			}
			var shared = _.intersects(v1, v2)
				,sumSq = 0;

			// calculate the square of the difference for each shared item	
			_.each(shared, function(item) {
				sumSq += pow((v1[item] - v2[item]), 2);
			});

			// return the square root of the sum.
			return sqrt(sumSq);
		};
		cluster.euclid = euclid;
		cluster.euclid.score = best().score;

		// v1, v2 are [] Arrays
		var pearson = function (vectors) {
			var v1 = vectors.v1
				,v2 = vectors.v2;

			// Nothing to correlate
			if (_.isEmpty(v1)) {
				return 0;
			}
			var	// Simple sums
				len = _.objectLength(v1)
				,sum1 = sum(v1)		
				,sum2 = sum(v2)
				// Sum of squares
				,sum1Sq	= sumSq(v1)		
				,sum2Sq = sumSq(v2)
				// Sum of products
				,pSum = sum(_.map(v1, function(item, i) {
					return (v2[i] ? item*v2[i] : 0);
				}))
				,num
				,score;

			// Calculate the Pearson score
			num = pSum - div((sum1*sum2), len);			
			score = sqrt((sum1Sq-div(pow(sum1,2), len)) * (sum2Sq-div(pow(sum2,2), len)));

			//console.log('num, score', num, score);						
			return (score === 0 ? 0 : div(num, score));
		};
		cluster.pearson = pearson;
		return cluster;
	};
	JSTEXT.similarity = similarity;
	
	
	// Web: http://norm.al/2009/04/14/list-of-english-stop-words/
	var stopwords = 'a,able,about,across,after,all,almost,also,am,among,an,and,any,are,as,at,be,because,been,but,by,can,cannot,could,dear,did,do,does,either,else,ever,every,for,from,get,got,had,has,have,he,her,hers,him,his,how,however,i,if,in,into,is,it,its,just,least,let,like,likely,may,me,might,most,must,my,neither,no,nor,not,of,off,often,on,only,or,other,our,own,rather,said,say,says,she,should,since,so,some,than,that,the,their,them,then,there,these,they,this,tis,to,too,twas,us,wants,was,we,were,what,when,where,which,while,who,whom,why,will,with,would,yet,you,your';
	
	var sentence = function (s) {
		var that = {}
		, sw = hash();

		// compile the stopwords into a hash
		stopwords.split(',').forEach(function( item ) {
			sw.store(item, 1);
		});

		that.sentence = s;
		// splits a string in to an array of keywords delimited by spaces;
		var tokenize = function (input) {
			return(input.toLowerCase().replace(/[^a-z0-9]+/g, ' ').split(' '));
		};

		// Removes stop words from input and returns a new object with the stopwords removed.
		var stopWords = function (input) {
			var words = input;
			/*jslint unparam: true */
			words.forEach(function(word, index) {
				if (sw.contains(word)) {
					delete words[index];
				}				
			});
			return _.compact(words);
		};

		// removes words shorter than 'min' from consideration. 
		// also removes numbers-only by default
		// accepts Optional 'max' parameter to filter long words
		// example: { num: true, min: 3 }
		var applyfilter = function(f, input) {			
			var num = (f && f.num) || true
			, max = (f && f.max) || undefined
			, min = (f && f.min) || 1
			, words = input;

			/*jslint unparam: true */
			words.forEach(function(word, index) {
				if (word.length < min || (max && word.length > max) ||
					(num === true && (word.replace(/[^a-z]+/g, '') === ''))) {
					delete words[index];
				}				
			});
			return _.compact(words);		
		};

		// Purpose: create DICTIONARY with stemmed words
		var stem = function (input) {
			var words = input
			, target = [];
			/*jslint unparam: true */
			words.forEach(function(word) {
				target.push(stemmer(word));				
			});
			return target;
		};
		that.stem = stem;

		var toHash = function (input) {
			var words = input
			, localHash = hash()
			, found;

			words.forEach(function(word) {
				found = localHash.lookup(word);
				if (found) {
					localHash.store(word, found+1);
				} else {
					localHash.store(word, 1);
				}
			});
			return localHash;
		};

		if (_.isString(s)) {
			return(toHash(stem(applyfilter({'min': 3, 'max': 25}, stopWords(tokenize(s))))));
		}
	};


	// Purpose: returns a DICTIONARY object with tokenized and stemmed words; provides a tfidf() method
	// for computing the selective value of a term in a document relative to a corpus.
	JSTEXT.text = function(s) {
		var that = {};
		
		that = _.extend(that, sentence(s || ''));

		// merges the dictionary from 'words' into 'target' and keeps a count of the
		// number of the occurrences of a word
		var merge = function (sources) {
			var target = sentence('corpus')
				, found
				, id;
						
			// for each document already stopped and stemmed
			_.each(sources, function(doc) {
				// now for each word, merge the hashes
				_.each(doc.values, function(value, word) {
					if (target.contains(word)) {
						target.set(word, target.get(word) + value);
					} else {
						target.set(word, doc.get(word));						
					}
				});						
			});
			return target;
		};
		that.merge = merge;
		
		var occurs = function (docs) {
			var target = hash();

			_.each(docs, function(s) {
				_.each(s.values, function(count, word) {
					if (target.contains(word)) {
						target.set(word, target.get(word)+1);
					} else {
						target.set(word, 1);
					}
				});
			});
			return target;
		};
		that.occurs = occurs;

		var stats = function (doc) {
			var count = 0
				, uniq = 0;

			_.each(doc.values, function(item) {
				count += item;
				uniq += 1;
			});

			return ({
				wordCount: count,
				uniqWords: uniq,
			});
		};
		that.stats = stats;

		// calculates tfidf for a document relative to a corpus 
		var frequencies = function (doc, corpusCounts, docOccurrences) {
			var target = hash()
			, id;

			// Purpose: compute the term-frequency, inverse document (tfidf) frequency for a
			// 'word' in a document relative to a 'corpus'
			// var tfidf = function (count, words_in_doc, total_docs, docs_with_term) {	
			_.each(doc.values, function(count, word) {
				
				target.set(word, computeTfidf(count, stats(doc).wordCount, 
													corpusCounts.getLength(), docOccurrences.get(word)));
			});
			return target;
		};
		that.frequencies = frequencies;

		// returns a list of the best hits to a query
		var bestHits = function (query, list) {
			var result = [];

			// for each document in the list
			list.forEach(function(doc) {
				// get the intersection of its word vector with the query
				result.push(dotProduct(doc.post(), query.post(), function(x) {
					return x;
				}));
			});	
			return result;					
		};
		that.bestHits = bestHits;
		return that;
	};

	
	JSTEXT.process = function(doclist) {
		var corpus = {}
		, text = JSTEXT.text();

		// convert sentences into a hash with word counts within the document
		corpus.doclist = _.map(doclist, function(s, id) {
			return _.text(s)
		});

		// create a hash to calculate the number of documents each word appears in
		corpus.occurrences = text.occurs(corpus.doclist);

		// merge the sentences into a corpus with the total word counts across all docs
		corpus.counts = text.merge(corpus.doclist);

		// using the corpus as a reference, calculate tfidf hash for each document
		corpus.tfidf = _.map(corpus.doclist, function (doc, index) {	
			return (text.frequencies(doc, corpus.counts, corpus.occurrences));
		});

		corpus.search = function (str) {
			var sources = _.map(corpus.doclist, function(v, index) { return index; })
			, results = text.bestHits(_.text(str), corpus.tfidf);

			return _.map(_.sortBy(_.zip(sources, results), function(result) {
				return result[1] * -1;
			}), _.item);
		};

		corpus.sort = function (sortedList) {
			var indices = _.map(sortedList, function(x) { return x[0] });

			return _.map(indices, function(value, index) {
				return doclist[sortedList[index][0]];
			});
		};

		return corpus;
	};
	
	_.mixin(JSTEXT);
	
}());	


/*

// converts a 'dictionary' index to list of Text() object
// generates a 'corpus'
// view: key: [ 'word', 'doc._id' ], value: {} 
var toText = function (result, iterator) {
	var docs = {}
		, corpus = text()
		, tmp
		, select = _.isFunction(iterator) ? iterator  : function (r) { 
				return ({'doc': r.key[1], 'word': r.key[0], 'value': r.value });
		};
	// for each row of the dictionary, get a word and optionally create a new doc
	result.each(function(row) {
		tmp = select(row);

		if (!docs[tmp.doc]) {
			docs[tmp.doc] = text();		// create the text object
			docs[tmp.doc].Id(tmp.doc);		// give the text object an id
		}
		docs[tmp.doc].store(tmp.word, tmp.value);
	});
	// combine all the docs into a corpus
	_.each(docs, function(doc) {
		corpus.merge(doc);
	});
	return(corpus);
};
that.toText = toText;

*/

