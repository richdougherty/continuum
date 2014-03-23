var util      = require('util'),
    continuum = require('../engine');

var print          = console.log,
    define         = continuum.utility.define,
    iterate        = continuum.utility.iterate,
    create         = continuum.utility.create,
    map            = continuum.utility.map,
    Queue          = continuum.utility.Queue,
    createFunction = continuum.createFunction;

var _push = [].push;


function path(path){
  if (typeof path === 'string') {
    return new Path(path);
  } else if (path instanceof Path) {
    return path;
  } else {
    return new Path(path+'');
  }
}


function Path(path){
  this.path = Path.normalize(path);
}

define(Path, [
  function normalize(path){}
]);


define(Path.prototype, [
  function isDirectory(){},
  function isFile(){},
  function exists(){},
  function dir(){},
  function read(){},
  function write(content){},
  function resolve(to){},
  function relativeTo(to){},
  function relativeFrom(from){},
  function basename(){},
  function extname(){},
  function dirname(){},
  function parts(){
    return this.path.split(/[\\\/]/);
  },
  function parent(){
    var dirname = this.dirname();
    if (dirname === this.path) {
      dirname = this.resolve('..');
    }
    return new Path(dirname || '/');
  },
  function children(){
    if (this.isDirectory()) {
      return this.dir().map(path);
    }
    throw new Error(this.path + ' is not a directory');
  },
  function toString(){
    return this.path;
  },
  function barename(){
    return this.basename().slice(0, -this.extname().length);
  }
]);

void function(){
  var fs   = require('fs'),
      path = require('path');

  define(Path, [
    function normalize(pathname){
      return path.resolve(pathname);
    }
  ]);

  define(Path.prototype, [
    function inspect(){
      return '<Path '+this.path+'>';
    },
    function stat(){
      var stat = fs.statSync(this.path);
      this.stat = function(){ return stat };
      return stat;
    },
    function isDirectory(){
      return this.stat().isDirectory();
    },
    function isFile(){
      return this.stat().isFile();
    },
    function exists(){
      return fs.existsSync(this.path);
    },
    function dir(){
      return fs.readdirSync(this.path).map(function(name){
        return path.resolve(this.path, name);
      }, this);
    },
    function read(){
      return fs.readFileSync(this.path, 'utf8');
    },
    function write(content){
      fs.writeFileSync(this.path, content);
    },
    function basename(){
      return path.basename(this.path);
    },
    function extname(){
      return path.extname(this.path);
    },
    function dirname(){
      return path.dirname(this.path);
    },
    function relativeTo(to){
      return path.relative(to, this.path);
    },
    function relativeFrom(from){
      return path.relative(this.path, to);
    },
    function resolve(to){
      return new Path(path.resolve.apply(null, [this.path].concat(to)));
    }
  ]);
}();


function stringify(o){
  return util.inspect(o);
}

function percent(n, t){
  return ((100 * n) / t).toFixed(2);
}

function isInt(n){
  return +n === (n | 0);
}

function escapeJS(source){
  return '"' + source.replace(/\\/g, '\\\\').replace(/(?!=\\)\r?\n/g, '\\n').replace(/"/g, '\\"') + '"';
}

function formatPath(name){
  return name.split(/\/|\\/).slice(3).join('/');
}


function fromObject(realm, object){
  var obj = realm.evaluate('({})');
  Object.keys(object).forEach(function(key){
    if (key !== 'test') {
      obj.Put(key, object[key]);
    }
  });
  return obj;
}


function toObject(o){
  if (o && o.Enumerate) {
    var out = {};
    var keys = o.Enumerate(false, true);
    for (var i=0; i < keys.length; i++) {
      var item = out[keys[i]] = o.get(keys[i]);
      if (item && item.Enumerate) {
        out[keys[i]] = toObject(item);
      }
    }
    return out;
  }
  return o;
}

var TestCase = (function(){
  var head = /(?:(?:\s*\/\/.*)?\s*\n)*/,
      comment = /\/\*\*?((?:\s|\S)*?)\*\/\s*\n/,
      any = /(?:\s|\S)*/g,
      placeholder = /\{\{(\w+)\}\}/,
      stars = /\s*\n\s*\*\s?/g,
      atattrs = /\s*\n\s*\*\s*@/,
      header = new RegExp('^'+head.source),
      record = new RegExp('^('+head.source+')(?:'+comment.source+')?('+any.source+')$');

  function stripStars(text){
    return text.replace(stars, '\n').trim();
  }

  function stripHeader(src){
    var match = src.match(header);
    return match ? src.slice(match[0].length) : src;
  }

  function parseTestRecord(obj, src, name){
    var match = src.match(record);

    if (!match) {
      throw new Error('unrecognized: '+name);
    }

    obj.test = match[3];

    if (match[2]) {
      var texts = match[2].split(atattrs);
      obj.commentary = stripStars(texts.shift());

      texts.forEach(function(text){
        var match = text.match(/^\w+/);

        if (!match) {
          throw new Error('Malformed "@" attribute: '+name);
        }

        match = match[0];

        if (match in obj) {
          throw new Error('duplicate: '+match);
        }

        obj[match] = stripStars(text.slice(match.length)).trim() || true;
      });
    }
  }

  function TestCase(filename, strict){
    this.file = path(filename);
    this.name = this.file.barename();
    parseTestRecord(this, this.file.read(), this.name);
  }

  define(TestCase.prototype, [
    function getSource(){
      var source = 'var strict_mode = ';
      if (this.strict || this.onlyStrict) {
        source = '"use strict";\n'+source+'true;\n';
      } else {
        source += 'false;\n';
      }
      return source + this.test + '\n';
    }
  ]);

  return TestCase;
})();

function TestRunner(suite, before, after) {
  var self = this;

  this.cache = create(null);
  this.suite = suite;

  define(this, {
    executeBefore: before || '',
    executeAfter: after || ''
  });

}

define(TestRunner.prototype, [
  function run(test){
    var realm   = continuum.createRealm(),
        src     = test.getSource(),
        current = realm.evaluate('({})');

    realm.on('throw', function(e){
      realm.global.set('iframeError', e.value);
    });

    for (var k in test) {
      if (typeof test[k] === 'string') {
        current.set(k, test[k]);
      }
    }


    function testRun(id, path, description, code, result, error){
      id !== undefined && current.set('id', id);
      path !== undefined && current.set('path', path);
      description !== undefined && current.set('description', description);
      result !== undefined && current.set('result', result);
      error !== undefined && current.set('error', error);
      code !== undefined && current.set('code', code);
    }

    function testFinished(){
      var result = current.get('result'),
          error = current.get('error');

      if (result === undefined) {
        current.set('result', 'fail');
        current.set('error', 'Failed to load test case (probable parse error).');
        current.set('description', 'Failed to load test case!');
      } else if (error !== undefined) {
        var msg = error.ConstructorName === 'Test262Error' ? '' : error.Get('name') + ": ";
        msg += error.Get('message');
        current.set('error', msg);
      } else if (error === undefined && result === 'fail') {
        current.set('error', 'Test case returned non-true value.');
      }
    }

    current.set('code', src);
    realm.evaluate(this.executeBefore);
    realm.global.set('testRun', createFunction(testRun));
    realm.global.set('testFinished', createFunction(testFinished));
    realm.global.set('testDescrip', current);
    realm.evaluate(src);
    realm.evaluate(this.executeAfter);

    var result = toObject(current);
    realm.global.destroy();
    return result;
  }
]);

var TestSuite = (function(){
  function TestSuiteOptions(o){
    if (o) {
      o = Object(o);
      for (var k in this) {
        if (k in o) {
          this[k] = o[k];
        }
      }
    }
  }

  TestSuiteOptions.prototype = {
    root: __dirname,
    strictOnly: false,
    nonStrictOnly: false,
    unmarkedDefault: false
  };


  function TestSuite(options){
    options = new TestSuiteOptions(options);
    var root = path(options.root).resolve(['..', 'third_party', 'test262', 'test']);
    this.tests = root.resolve('suite');
    this.libs = root.resolve('harness');
    this.strictOnly = options.strictOnly;
    this.nonStrictOnly = options.nonStrictOnly;
    this.unmarkedDefault = options.unmarkedDefault;
    this.queue = new Queue;
    this.results = {};

    if (!this.tests.exists()) {
      throw new Error('No test repository found');
    }

    if (!this.libs.exists()) {
      throw new Error('No test library found');
    }

    var before = map(['cth.js', 'sta.js', 'testBuiltInObject.js'], function(name){
      return this.libs.resolve(name).read();
    }, this).join('\n\n');

    var after = this.libs.resolve('gs.js').read();
    this.runner = new TestRunner(this, before, after);

    Object.defineProperty(this, 'includes', {
      get: function(){ return includes }
    });
  }


  define(TestSuite.prototype, [
    function summary(progress) {
      print();
      print("=== Summary ===");
      print(" - Ran %d tests", progress.count);
      if (progress.failed === 0) {
        print(" - All tests succeeded");
      } else {
        print(" - Passed %d tests (%d)", progress.succeeded, percent(progress.succeeded, progress.count));
        print(" - Failed %d tests (%d)", progress.failed, percent(progress.failed, progress.count));
      }
    },
    function enqueue(file){
      if (this.queue.length >= this.max) return this;
      file = path(file);
      if (file.isDirectory()) {
        file.children().forEach(this.enqueue, this);
      } else {
        this.queue.push(file);
      }
      return this;
    },
    function chapter(chapter){
      chapter = chapter.toString().split('.');
      var file = this.tests.resolve('ch' + ('00'+ (chapter[0] | 0)).slice(-2));
      if (chapter[1]) {
        file = file.resolve(chapter[0] + '.' + chapter[1]);
      }
      if (chapter[2]) {
        file = file.resolve(chapter[0] + '.' + chapter[1] + '.' + chapter[2]);
      }
      if (file.exists()) {
        this.enqueue(file);
      }
      return this;
    },
    function next(){
      var item = this.queue.shift();
      if (item) {
        var test = new TestCase(item, this.strict);

        test.paths = test.file.parts();

        test.paths.reduce(function(r, s, i, a){
          if (!(s in r)) {
            if (i === a.length - 1) {
              r[s] = test;
            } else {
              r[s] = {};
            }
          }
          return r[s];
        }, this.results);

        return this.runner.run(test);
      }
    },
    function run(count){
      count = +count || Math.min(40, this.queue.length);
      var record = path(__dirname+'/tested.json');
      var tested = record.exists() ? require(record.path) : {};

      while (count-- && this.queue.length) {
        var name = formatPath(this.queue.front().relativeTo(__dirname));
        if (name in tested) {
          this.queue.shift();
          count++;
          continue;
        }

        var result = tested[name] = this.next();
        if (result) {
          if (result.result === 'pass') {
            tested[name] = 'pass';
          } else {
            delete result.abspath;
            delete result.path;
            delete result.paths;
            delete result.code;
            delete result.test;
            delete result.name;
          }
        }
        record.write(JSON.stringify(tested, null, '  '));
      }

      return tested;
    }
  ]);

  return TestSuite;
})();

var x = new TestSuite;
x.chapter('11');
print(x.run());
