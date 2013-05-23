##js-text

js-text provides methods for analyzing strings of text, including [stopword](http://en.wikipedia.org/wiki/Stop_words) removal and [stemming](http://en.wikipedia.org/wiki/Stemming) and produces objects containing word counts and [frequencies](http://en.wikipedia.org/wiki/Tf%E2%80%93idf). Results are produced for a single string or collection of strings (a corpus). Once the frequencies have been calculated for a set of documents relative to a corpus (a vector), a similarity score can be computed as from the [dot product](http://en.wikipedia.org/wiki/Dot_product) of the two vectors. These routines are very useful for rudimentary text mining and document clustering.

###Dependencies

* [underscore](underscore.org)
* [js-base](https://github.com/rranauro/js-base)
* [js-hash](https://github.com/rranauro/js-hash)
* [porter](https://github.com/jedp/porter-stemmer)

###Summary

* [text](#text) - takes a string, removes stop words, stems each word, and produces a hash object of words and the number of times they appear in the string.
	* [occurs](#occurs) - for a set of strings, counts to number of documents a word occurring
	* [merge](#merge) - merges a set of strings into a single corpus and counts the occurrences of words for all strings.
	* [tfidf](#tfidf) - for a string, counts the [tfidf](http://en.wikipedia.org/wiki/Tf%E2%80%93idf) relative to a set of strings.
* [process](#process) - produces methods for calculating frequencies and finding the best hit for a string from a set of strings (aka documents).
	* [search](#search) - computes a similarity score for a query string against a set of strings
	* [sort](#sort) - sorts the output of a search


###Methods

<a name="text" />
#####text(str)

*Takes a string, removes [stopwords](http://en.wikipedia.org/wiki/Stop_words) [stems each word](http://en.wikipedia.org/wiki/Stemming)  and returns a hash words/counts.*


	// Example
	require('js-hash');
	var text = _.text('a quick brown fox ran cirles'); 
	console.log(text.keys(), text.values);
	// -> [ 'quick', 'brown', 'fox', 'ran', 'circl' ] [ 1, 2, 1, 1, 1 ]

> Note: js-text does not introduce new global variables. Instead it is mixed into Underscore and is accessed off the [underscore](underscore.org) variable.

<a name="occurs" />
######occurs(list)

*Takes an array of computed [hashes](#text) and returns a hash containing a list of words and a count of the number of documents where the words occur.*

	// Example
	var occur = _.text().occurs([_.text('a quick brown fox ran cirles')]);
	console.log(occur);
	// -> { quick: 1, brown: 1, fox: 1, ran: 1, circl: 1 }

<a name="occurs" />	
######merge(list)

*Takes an array of computed [hashes](#text) and returns a hash containing a list of words and a count of the number of documents where the words occur.*

<a name="occurs" />
######tfidf(list)

*Takes an array of computed [hashes](#text) and returns a hash containing the list of words and the computed tfidf relative to the entire corpus.*

<a name="process" />
#####process(doclist)

*Takes an array of strings and produces and object with methods for calculating frequencies and finding the best hit for a string from a set of strings (aka documents).*

######search(str)

*Searches a string against a pre-processed set of strings to calculate similarity. Returns an array with the ranking and the computed similarity value.

######sort(searchOutput)

*sorts the output of a search.*

###Install

TBD

###License

Apache

