var debug = (function(exports){

  var utility = require('./utility'),
      inherit = utility.inherit,
      create = utility.create,
      define = utility.define;

  var constants = require('./constants'),
      ENUMERABLE = constants.ATTRIBUTES.ENUMERABLE,
      CONFIGURABLE = constants.ATTRIBUTES.CONFIGURABLE,
      WRITABLE = constants.ATTRIBUTES.WRITABLE,
      ACCESSOR = constants.ATTRIBUTES.ACCESSOR;

  var Continuum = require('./runtime').Continuum



  function always(value){
    return function(){ return value };
  }

  function alwaysCall(func, args){
    args || (args = []);
    return function(){ return func.apply(null, args) }
  }


  function Mirror(){}

  define(Mirror.prototype, {
    type: null,
    getPrototype: function(){
      return _Null;
    },
    get: function(){
      return _Undefined;
    },
    kind: 'Unknown',
    label: always(''),
    hasOwn: always(null),
    has: always(null),
    list: alwaysCall(Array),
    inheritedAttrs: alwaysCall(create, [null]),
    ownAttrs: alwaysCall(create, [null]),
    isExtensible: always(null),
    isEnumerable: always(null),
    isConfigurable: always(null),
    isAccessor: always(null),
    isWritable: always(null),
    propAttributes: always(null)
  });

  function brand(v){
    return Object.prototype.toString.call(v).slice(8, -1);
  }

  function MirrorValue(subject, label){
    this.subject = subject;
    this.type = typeof subject;
    this.kind = brand(subject)+'Value';
    this.label = always(label);
  }

  inherit(MirrorValue, Mirror);

  function MirrorStringValue(subject){
    this.subject = subject;
  }

  inherit(MirrorStringValue, MirrorValue, {
    label: always('string'),
    kind: 'StringValue',
    type: 'string'
  });

  function MirrorNumberValue(subject){
    this.subject = subject;
  }

  inherit(MirrorNumberValue, MirrorValue, {
    label: always('number'),
    kind: 'NumberValue',
    type: 'number'
  });





  function MirrorObject(subject){
    subject.__introspected = this;
    this.subject = subject;
    this.attrs = subject.attributes;
    this.props = subject.properties;
  }

  inherit(MirrorObject, Mirror, {
    kind: 'Object',
    type: 'object',
    attrs: null,
    props: null
  }, [
    function get(key){
      if (this.isPropAccessor(key)) {
        return introspect(this.subject.Get(key));
      } else {
        return introspect(this.props[key]);
      }
    },
    function getValue(key){
      return this.get(key).subject;
    },
    function getPrototype(){
      return introspect(this.subject.GetPrototype());
    },
    function hasOwn(key){
      if (this.props) {
        return key in this.props;
      } else {
        return false;
      }
    },
    function has(key){
      if (this.props) {
        return key in this.props ? true : this.getPrototype().has(key);
      } else {
        return false;
      }
    },
    function isExtensible(key){
      return this.subject.GetExtensible();
    },
    function isPropEnumerable(key){
      return (this.attrs[key] & ENUMERABLE) > 0;
    },
    function isPropConfigurable(key){
      return (this.attrs[key] & CONFIGURABLE) > 0;
    },
    function isPropAccessor(key){
      return (this.attrs[key] & ACCESSOR) > 0;
    },
    function isPropWritable(key){
      return !!(this.isPropAccessor(key) ? this.props[key].Set : this.attrs[key] & WRITABLE);
    },
    function propAttributes(key){
      return this.attrs[key];
    },
    function label(){
      if (this.subject.ConstructorName) {
        return this.subject.ConstructorName;
      } else if (this.has('constructor')) {
        var ctorName = this.get('constructor').get('name');
        if (ctorName.subject && typeof ctorName.subject === 'string') {
          return ctorName.subject;
        }
      }

      if (this.subject.NativeBrand) {
        return this.subject.NativeBrand.name;
      }

      return 'Object';
    },
    function inheritedAttrs(obj){
      if (obj) {
        this.getPrototype().inheritedAttrs(obj);
        return this.ownAttrs(obj);
      } else {
        return this.getPrototype().inheritedAttrs(obj);
      }
    },
    function ownAttrs(obj){
      obj || (obj = create(null));
      for (var k in this.props) {
        obj[k] = this.attrs[k];
      }
      return obj;
    },
    function list(own, hidden){
      var props = own ? this.ownAttrs() : this.inheritedAttrs(),
          keys = [];

      for (var k in props) {
        if (hidden || props[k] & ENUMERABLE) {
          keys.push(k);
        }
      }

      return keys.sort();
    }
  ]);


  function MirrorArray(subject){
    MirrorObject.call(this, subject);
  }

  inherit(MirrorArray, MirrorObject, {
    kind: 'Array'
  }, [
    function list(own, hidden){
      var props = own ? this.ownAttrs() : this.inheritedAttrs(),
          len = this.getValue('length'),
          indexes = [],
          keys = [];

      for (var i=0; i < len; i++) {
        indexes.push(i+'');
      }
      indexes.push('length');

      for (var k in props) {
        if (hidden || props[k] & ENUMERABLE) {
          if (k !== 'length' && !utility.isInteger(+k)) {
            keys.push(k);
          }
        }
      }

      return indexes.concat(keys.sort());
    }
  ]);


  function MirrorBoolean(subject){
    MirrorObject.call(this, subject);
  }

  inherit(MirrorBoolean, MirrorObject, {
    kind: 'Boolean'
  }, [
  ]);

  function MirrorDate(subject){
    MirrorObject.call(this, subject);
  }

  inherit(MirrorDate, MirrorObject, {
    kind: 'Date'
  }, [
  ]);


  function MirrorError(subject){
    MirrorObject.call(this, subject);
  }

  inherit(MirrorError, MirrorObject, {
    kind: 'Error'
  }, [
  ]);


  function MirrorFunction(subject){
    MirrorObject.call(this, subject);
  }

  inherit(MirrorFunction, MirrorObject, {
    type: 'function',
    kind: 'Function'
  });


  function MirrorMap(subject){
    MirrorObject.call(this, subject);
  }

  inherit(MirrorMap, MirrorObject, {
    kind: 'Map'
  }, [
  ]);


  function MirrorNumber(subject){
    MirrorObject.call(this, subject);
  }

  inherit(MirrorNumber, MirrorObject, {
    kind: 'Number'
  }, [
  ]);

  function MirrorRegExp(subject){
    MirrorObject.call(this, subject);
  }

  inherit(MirrorRegExp, MirrorObject, {
    kind: 'RegExp'
  }, [
  ]);


  function MirrorSet(subject){
    MirrorObject.call(this, subject);
  }

  inherit(MirrorSet, MirrorObject, {
    kind: 'Set'
  }, [
  ]);


  function MirrorString(subject){
    MirrorObject.call(this, subject);
  }

  inherit(MirrorString, MirrorObject,{
    kind: 'String'
  }, [
    function get(key){
      if (key < this.props.length && key >= 0) {
        return this.subject.PrimitiveValue[key];
      } else if (this.isPropAccessor(key)) {
        return introspect(this.subject.Get(key));
      } else {
        return introspect(this.props[key]);
      }
    },
    function ownAttrs(obj){
      obj || (obj = create(null));
      for (var i=0; i < this.props.length; i++) {
        obj[i] = 1;
      }
      for (var k in this.props) {
        obj[k] = this.attrs[k];
      }
      return obj;
    },
  ]);


  function MirrorWeakMap(subject){
    MirrorObject.call(this, subject);
  }

  inherit(MirrorWeakMap, MirrorObject, {
    kind: 'WeakMap'
  }, [
  ]);



  function MirrorProxy(subject){
    this.subject = subject;
    if ('Call' in subject) {
      this.type = 'function';
    }
    this.kind = introspect(subject.Target).kind;
  }

  inherit(MirrorProxy, Mirror, {
    type: 'object'
  }, [
    MirrorObject.prototype.isExtensible,
    MirrorObject.prototype.getPrototype,
    MirrorObject.prototype.list,
    function label(){
      return 'Proxy' + MirrorObject.prototype.label.call(this);
    },
    function get(key){
      this.refresh(key);
      return introspect(this.props[key]);
    },
    function hasOwn(key){
      return this.refresh(key);
    },
    function has(key){
      return this.refresh(key) ? true : this.getPrototype().has(key);
    },
    function isPropEnumerable(key){
      if (this.refresh(key)) {
        return (this.attrs[key] & ENUMERABLE) > 0;
      } else {
        return false;
      }
    },
    function isPropConfigurable(key){
      if (this.refresh(key)) {
        return (this.attrs[key] & CONFIGURABLE) > 0;
      } else {
        return false;
      }
    },
    function isPropAccessor(key){
      if (this.refresh(key)) {
        return (this.attrs[key] & ACCESSOR) > 0;
      } else {
        return false;
      }
    },
    function isPropWritable(key){
      if (this.refresh(key)) {
        return !!(this.isAccessor() ? this.props[key].Set : this.attrs[key] & WRITABLE);
      } else {
        return false;
      }
    },
    function propAttributes(key){
      if (this.refresh(key)) {
        return this.attrs[key];
      } else {
        return false;
      }
    },
    function inheritedAttrs(obj){
      if (obj) {
        this.getPrototype().inheritedAttrs(obj);
        return this.ownAttrs(obj);
      } else {
        return this.getPrototype().inheritedAttrs(obj);
      }
    },
    function ownAttrs(obj){
      var key, keys = this.subject.GetOwnPropertyNames();

      obj || (obj = create(null));
      this.props = create(null);
      this.attrs = create(null);

      for (var i=0; i < keys.length; i++) {
        key = keys[i];
        if (this.refresh(key)) {
          obj[key] = this.attrs[key];
        }
      }

      return obj;
    },
    function refresh(key){
      if (!(key in this.attrs)) {
        var desc = this.subject.GetOwnProperty(key, false);
        if (desc) {
          if ('Value' in desc) {
            this.attrs[key] = desc.Enumerable | (desc.Configurable << 1) | (desc.Writable << 2);
            this.props[key] = desc.Value;
          } else {
            this.attrs[key] = desc.Enumerable | (desc.Configurable << 1) | A;
            this.props[key] = { Get: desc.Get, Set: desc.Set };
          }
          return true;
        } else {
          delete this.attrs[key];
          delete this.props[key];
        }
      }
      return false;
    }
  ]);


  var brands = {
    Array   : MirrorArray,
    Boolean : MirrorBoolean,
    Date    : MirrorDate,
    Error   : MirrorError,
    Function: MirrorFunction,
    Map     : MirrorMap,
    Number  : MirrorNumber,
    RegExp  : MirrorRegExp,
    Set     : MirrorSet,
    String  : MirrorString,
    WeakMap : MirrorWeakMap
  };

  var _Null        = new MirrorValue(null, 'null'),
      _Undefined   = new MirrorValue(undefined, 'undefined'),
      _True        = new MirrorValue(true, 'true'),
      _False       = new MirrorValue(false, 'false'),
      _NaN         = new MirrorValue(NaN, 'NaN'),
      _Infinity    = new MirrorValue(Infinity, 'Infinity'),
      _NegInfinity = new MirrorValue(-Infinity, '-Infinity'),
      _Zero        = new MirrorValue(0, '0'),
      _NegZero     = new MirrorValue(-0, '-0'),
      _One         = new MirrorValue(1, '1'),
      _NegOne      = new MirrorValue(-1, '-1'),
      _Empty       = new MirrorValue('', "''");

  var numbers = create(null),
      strings = create(null);


  function introspect(subject){
    switch (typeof subject) {
      case 'undefined': return _Undefined;
      case 'boolean': return subject ? _True : _False;
      case 'string':
        if (subject === '') {
          return _Empty
        } else if (subject.length < 20) {
          if (subject in strings) {
            return strings[subject];
          } else {
            return strings[subject] = new MirrorStringValue(subject);
          }
        } else {
          return new MirrorStringValue(subject);
        }
      case 'number':
        if (subject !== subject) {
          return _NaN;
        }
        switch (subject) {
          case Infinity: return _Infinity;
          case -Infinity: return _NegInfinity;
          case 0: return 1 / subject === -Infinity ? _NegZero : _Zero;
          case 1: return _One;
          case -1: return _NegOne;
        }
        if (subject in numbers) {
          return numbers[subject];
        } else {
          return numbers[subject] = new MirrorNumberValue(subject);
        }
      case 'object':
        if (subject === null) {
          return _Null;
        }
        if (subject instanceof Mirror) {
          return subject;
        }
        if (subject.__introspected) {
          return subject.__introspected;
        }
        if (!subject.isProxy) {
          var Ctor = subject.NativeBrand in brands
                    ? brands[subject.NativeBrand]
                    : 'Call' in subject
                      ? MirrorFunction
                      : MirrorObject;

          return new Ctor(subject);
        } else {
          return new MirrorProxy(subject);
        }
    }
  }



  function Renderer(handlers){
    if (handlers) {
      for (var k in this) {
        if (k in handlers) {
          this[k] = handlers[k];
        }
      }
    }
  }

  Renderer.prototype = {
    Unknown: function(mirror){
      return 'unknown!?';
    },
    BooleanValue: function(mirror){
      return mirror.label();
    },
    StringValue: function(mirror){
      return utility.quotes(mirror.subject);
    },
    NumberValue: function(mirror){
      var label = mirror.label();
      return label === 'number' ? mirror.subject : label;
    },
    UndefinedValue: function(mirror){
      return mirror.label();
    },
    NullValue: function(mirror){
      return mirror.label();
    },
    Array: function(mirror){
      return mirror.label();
    },
    Boolean: function(mirror){
      return mirror.label();
    },
    Date: function(mirror){
      return mirror.label();
    },
    Error: function(mirror){
      return mirror.getValue('name') + ': ' + mirror.getValue('message');
    },
    Function: function(mirror){
      return mirror.label();
    },
    Map: function(mirror){
      return mirror.label();
    },
    Object: function(mirror){
      return mirror.label();
    },
    Number: function(mirror){
      return mirror.label();
    },
    RegExp: function(mirror){
      return mirror.label();
    },
    Set: function(mirror){
      return mirror.label();
    },
    String: function(mirror){
      return mirror.label();
    },
    WeakMap: function(mirror){
      return mirror.label();
    }
  };

  define(Renderer.prototype, [
    function render(subject){
      var mirror = introspect(subject);
      return this[mirror.kind](mirror);
    }
  ]);


  var renderer = new Renderer;

  function render(o){
    return renderer.render(o);
  }

  function createRenderer(handlers){
    return new Renderer(handlers);
  }

  function isMirror(o){
    return o instanceof Mirror;
  }

  exports.createRenderer = createRenderer;
  exports.basicRenderer = render;
  exports.introspect = introspect;
  exports.isMirror = isMirror;
  exports.Renderer = Renderer;

  return exports;
})(typeof module !== 'undefined' ? module.exports : {});