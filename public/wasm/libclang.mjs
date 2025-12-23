// This code implements the `-sMODULARIZE` settings by taking the generated
// JS program code (INNER_JS_CODE) and wrapping it in a factory function.

// When targetting node and ES6 we use `await import ..` in the generated code
// so the outer function needs to be marked as async.
async function Module(moduleArg = {}) {
  var moduleRtn;

// include: shell.js
// include: minimum_runtime_check.js
(function() {
  // "30.0.0" -> 300000
  function humanReadableVersionToPacked(str) {
    str = str.split('-')[0]; // Remove any trailing part from e.g. "12.53.3-alpha"
    var vers = str.split('.').slice(0, 3);
    while(vers.length < 3) vers.push('00');
    vers = vers.map((n, i, arr) => n.padStart(2, '0'));
    return vers.join('');
  }
  // 300000 -> "30.0.0"
  var packedVersionToHumanReadable = n => [n / 10000 | 0, (n / 100 | 0) % 100, n % 100].join('.');

  var TARGET_NOT_SUPPORTED = 2147483647;

  // Note: We use a typeof check here instead of optional chaining using
  // globalThis because older browsers might not have globalThis defined.
  var currentNodeVersion = typeof process !== 'undefined' && process.versions?.node ? humanReadableVersionToPacked(process.versions.node) : TARGET_NOT_SUPPORTED;
  if (currentNodeVersion < 160000) {
    throw new Error(`This emscripten-generated code requires node v${ packedVersionToHumanReadable(160000) } (detected v${packedVersionToHumanReadable(currentNodeVersion)})`);
  }

  var userAgent = typeof navigator !== 'undefined' && navigator.userAgent;
  if (!userAgent) {
    return;
  }

  var currentSafariVersion = userAgent.includes("Safari/") && !userAgent.includes("Chrome/") && userAgent.match(/Version\/(\d+\.?\d*\.?\d*)/) ? humanReadableVersionToPacked(userAgent.match(/Version\/(\d+\.?\d*\.?\d*)/)[1]) : TARGET_NOT_SUPPORTED;
  if (currentSafariVersion < 150000) {
    throw new Error(`This emscripten-generated code requires Safari v${ packedVersionToHumanReadable(150000) } (detected v${currentSafariVersion})`);
  }

  var currentFirefoxVersion = userAgent.match(/Firefox\/(\d+(?:\.\d+)?)/) ? parseFloat(userAgent.match(/Firefox\/(\d+(?:\.\d+)?)/)[1]) : TARGET_NOT_SUPPORTED;
  if (currentFirefoxVersion < 79) {
    throw new Error(`This emscripten-generated code requires Firefox v79 (detected v${currentFirefoxVersion})`);
  }

  var currentChromeVersion = userAgent.match(/Chrome\/(\d+(?:\.\d+)?)/) ? parseFloat(userAgent.match(/Chrome\/(\d+(?:\.\d+)?)/)[1]) : TARGET_NOT_SUPPORTED;
  if (currentChromeVersion < 85) {
    throw new Error(`This emscripten-generated code requires Chrome v85 (detected v${currentChromeVersion})`);
  }
})();

// end include: minimum_runtime_check.js
// The Module object: Our interface to the outside world. We import
// and export values on it. There are various ways Module can be used:
// 1. Not defined. We create it here
// 2. A function parameter, function(moduleArg) => Promise<Module>
// 3. pre-run appended it, var Module = {}; ..generated code..
// 4. External script tag defines var Module.
// We need to check if Module already exists (e.g. case 3 above).
// Substitution will be replaced with actual code on later stage of the build,
// this way Closure Compiler will not mangle it (e.g. case 4. above).
// Note that if you want to run closure, and also to use Module
// after the generated code, you will need to define   var Module = {};
// before the code. Then that object will be used in the code, and you
// can continue to use Module afterwards as well.
var Module = moduleArg;

// Determine the runtime environment we are in. You can customize this by
// setting the ENVIRONMENT setting at compile time (see settings.js).

// Attempt to auto-detect the environment
var ENVIRONMENT_IS_WEB = !!globalThis.window;
var ENVIRONMENT_IS_WORKER = !!globalThis.WorkerGlobalScope;
// N.b. Electron.js environment is simultaneously a NODE-environment, but
// also a web environment.
var ENVIRONMENT_IS_NODE = globalThis.process?.versions?.node && globalThis.process?.type != 'renderer';
var ENVIRONMENT_IS_SHELL = !ENVIRONMENT_IS_WEB && !ENVIRONMENT_IS_NODE && !ENVIRONMENT_IS_WORKER;

if (ENVIRONMENT_IS_NODE) {
  // When building an ES module `require` is not normally available.
  // We need to use `createRequire()` to construct the require()` function.
  const { createRequire } = await import('module');
  /** @suppress{duplicate} */
  var require = createRequire(import.meta.url);

}

// --pre-jses are emitted after the Module integration code, so that they can
// refer to Module (if they choose; they can also define Module)


var arguments_ = [];
var thisProgram = './this.program';
var quit_ = (status, toThrow) => {
  throw toThrow;
};

var _scriptName = import.meta.url;

// `/` should be present at the end if `scriptDirectory` is not empty
var scriptDirectory = '';
function locateFile(path) {
  if (Module['locateFile']) {
    return Module['locateFile'](path, scriptDirectory);
  }
  return scriptDirectory + path;
}

// Hooks that are implemented differently in different runtime environments.
var readAsync, readBinary;

if (ENVIRONMENT_IS_NODE) {
  const isNode = globalThis.process?.versions?.node && globalThis.process?.type != 'renderer';
  if (!isNode) throw new Error('not compiled for this environment (did you build to HTML and try to run it not on the web, or set ENVIRONMENT to something - like node - and run it someplace else - like on the web?)');

  // These modules will usually be used on Node.js. Load them eagerly to avoid
  // the complexity of lazy-loading.
  var fs = require('fs');

  if (_scriptName.startsWith('file:')) {
    scriptDirectory = require('path').dirname(require('url').fileURLToPath(_scriptName)) + '/';
  }

// include: node_shell_read.js
readBinary = (filename) => {
  // We need to re-wrap `file://` strings to URLs.
  filename = isFileURI(filename) ? new URL(filename) : filename;
  var ret = fs.readFileSync(filename);
  assert(Buffer.isBuffer(ret));
  return ret;
};

readAsync = async (filename, binary = true) => {
  // See the comment in the `readBinary` function.
  filename = isFileURI(filename) ? new URL(filename) : filename;
  var ret = fs.readFileSync(filename, binary ? undefined : 'utf8');
  assert(binary ? Buffer.isBuffer(ret) : typeof ret == 'string');
  return ret;
};
// end include: node_shell_read.js
  if (process.argv.length > 1) {
    thisProgram = process.argv[1].replace(/\\/g, '/');
  }

  arguments_ = process.argv.slice(2);

  quit_ = (status, toThrow) => {
    process.exitCode = status;
    throw toThrow;
  };

} else
if (ENVIRONMENT_IS_SHELL) {

} else

// Note that this includes Node.js workers when relevant (pthreads is enabled).
// Node.js workers are detected as a combination of ENVIRONMENT_IS_WORKER and
// ENVIRONMENT_IS_NODE.
if (ENVIRONMENT_IS_WEB || ENVIRONMENT_IS_WORKER) {
  try {
    scriptDirectory = new URL('.', _scriptName).href; // includes trailing slash
  } catch {
    // Must be a `blob:` or `data:` URL (e.g. `blob:http://site.com/etc/etc`), we cannot
    // infer anything from them.
  }

  if (!(globalThis.window || globalThis.WorkerGlobalScope)) throw new Error('not compiled for this environment (did you build to HTML and try to run it not on the web, or set ENVIRONMENT to something - like node - and run it someplace else - like on the web?)');

  {
// include: web_or_worker_shell_read.js
if (ENVIRONMENT_IS_WORKER) {
    readBinary = (url) => {
      var xhr = new XMLHttpRequest();
      xhr.open('GET', url, false);
      xhr.responseType = 'arraybuffer';
      xhr.send(null);
      return new Uint8Array(/** @type{!ArrayBuffer} */(xhr.response));
    };
  }

  readAsync = async (url) => {
    // Fetch has some additional restrictions over XHR, like it can't be used on a file:// url.
    // See https://github.com/github/fetch/pull/92#issuecomment-140665932
    // Cordova or Electron apps are typically loaded from a file:// url.
    // So use XHR on webview if URL is a file URL.
    if (isFileURI(url)) {
      return new Promise((resolve, reject) => {
        var xhr = new XMLHttpRequest();
        xhr.open('GET', url, true);
        xhr.responseType = 'arraybuffer';
        xhr.onload = () => {
          if (xhr.status == 200 || (xhr.status == 0 && xhr.response)) { // file URLs can return 0
            resolve(xhr.response);
            return;
          }
          reject(xhr.status);
        };
        xhr.onerror = reject;
        xhr.send(null);
      });
    }
    var response = await fetch(url, { credentials: 'same-origin' });
    if (response.ok) {
      return response.arrayBuffer();
    }
    throw new Error(response.status + ' : ' + response.url);
  };
// end include: web_or_worker_shell_read.js
  }
} else
{
  throw new Error('environment detection error');
}

var out = console.log.bind(console);
var err = console.error.bind(console);

var IDBFS = 'IDBFS is no longer included by default; build with -lidbfs.js';
var PROXYFS = 'PROXYFS is no longer included by default; build with -lproxyfs.js';
var WORKERFS = 'WORKERFS is no longer included by default; build with -lworkerfs.js';
var FETCHFS = 'FETCHFS is no longer included by default; build with -lfetchfs.js';
var ICASEFS = 'ICASEFS is no longer included by default; build with -licasefs.js';
var JSFILEFS = 'JSFILEFS is no longer included by default; build with -ljsfilefs.js';
var OPFS = 'OPFS is no longer included by default; build with -lopfs.js';

var NODEFS = 'NODEFS is no longer included by default; build with -lnodefs.js';

// perform assertions in shell.js after we set up out() and err(), as otherwise
// if an assertion fails it cannot print the message

assert(!ENVIRONMENT_IS_SHELL, 'shell environment detected but not enabled at build time.  Add `shell` to `-sENVIRONMENT` to enable.');

// end include: shell.js

// include: preamble.js
// === Preamble library stuff ===

// Documentation for the public APIs defined in this file must be updated in:
//    site/source/docs/api_reference/preamble.js.rst
// A prebuilt local version of the documentation is available at:
//    site/build/text/docs/api_reference/preamble.js.txt
// You can also build docs locally as HTML or other formats in site/
// An online HTML version (which may be of a different version of Emscripten)
//    is up at http://kripken.github.io/emscripten-site/docs/api_reference/preamble.js.html

var wasmBinary;

if (!globalThis.WebAssembly) {
  err('no native wasm support detected');
}

// Wasm globals

//========================================
// Runtime essentials
//========================================

// whether we are quitting the application. no code should run after this.
// set in exit() and abort()
var ABORT = false;

// set by exit() and abort().  Passed to 'onExit' handler.
// NOTE: This is also used as the process return code code in shell environments
// but only when noExitRuntime is false.
var EXITSTATUS;

// In STRICT mode, we only define assert() when ASSERTIONS is set.  i.e. we
// don't define it at all in release modes.  This matches the behaviour of
// MINIMAL_RUNTIME.
// TODO(sbc): Make this the default even without STRICT enabled.
/** @type {function(*, string=)} */
function assert(condition, text) {
  if (!condition) {
    abort('Assertion failed' + (text ? ': ' + text : ''));
  }
}

// We used to include malloc/free by default in the past. Show a helpful error in
// builds with assertions.

/**
 * Indicates whether filename is delivered via file protocol (as opposed to http/https)
 * @noinline
 */
var isFileURI = (filename) => filename.startsWith('file://');

// include: runtime_common.js
// include: runtime_stack_check.js
// Initializes the stack cookie. Called at the startup of main and at the startup of each thread in pthreads mode.
function writeStackCookie() {
  var max = _emscripten_stack_get_end();
  assert((max & 3) == 0);
  // If the stack ends at address zero we write our cookies 4 bytes into the
  // stack.  This prevents interference with SAFE_HEAP and ASAN which also
  // monitor writes to address zero.
  if (max == 0) {
    max += 4;
  }
  // The stack grow downwards towards _emscripten_stack_get_end.
  // We write cookies to the final two words in the stack and detect if they are
  // ever overwritten.
  HEAPU32[((max)>>2)] = 0x02135467;
  HEAPU32[(((max)+(4))>>2)] = 0x89BACDFE;
  // Also test the global address 0 for integrity.
  HEAPU32[((0)>>2)] = 1668509029;
}

function checkStackCookie() {
  if (ABORT) return;
  var max = _emscripten_stack_get_end();
  // See writeStackCookie().
  if (max == 0) {
    max += 4;
  }
  var cookie1 = HEAPU32[((max)>>2)];
  var cookie2 = HEAPU32[(((max)+(4))>>2)];
  if (cookie1 != 0x02135467 || cookie2 != 0x89BACDFE) {
    abort(`Stack overflow! Stack cookie has been overwritten at ${ptrToString(max)}, expected hex dwords 0x89BACDFE and 0x2135467, but received ${ptrToString(cookie2)} ${ptrToString(cookie1)}`);
  }
  // Also test the global address 0 for integrity.
  if (HEAPU32[((0)>>2)] != 0x63736d65 /* 'emsc' */) {
    abort('Runtime error: The application has corrupted its heap memory area (address zero)!');
  }
}
// end include: runtime_stack_check.js
// include: runtime_exceptions.js
// end include: runtime_exceptions.js
// include: runtime_debug.js
var runtimeDebug = true; // Switch to false at runtime to disable logging at the right times

// Used by XXXXX_DEBUG settings to output debug messages.
function dbg(...args) {
  if (!runtimeDebug && typeof runtimeDebug != 'undefined') return;
  // TODO(sbc): Make this configurable somehow.  Its not always convenient for
  // logging to show up as warnings.
  console.warn(...args);
}

// Endianness check
(() => {
  var h16 = new Int16Array(1);
  var h8 = new Int8Array(h16.buffer);
  h16[0] = 0x6373;
  if (h8[0] !== 0x73 || h8[1] !== 0x63) abort('Runtime error: expected the system to be little-endian! (Run with -sSUPPORT_BIG_ENDIAN to bypass)');
})();

function consumedModuleProp(prop) {
  if (!Object.getOwnPropertyDescriptor(Module, prop)) {
    Object.defineProperty(Module, prop, {
      configurable: true,
      set() {
        abort(`Attempt to set \`Module.${prop}\` after it has already been processed.  This can happen, for example, when code is injected via '--post-js' rather than '--pre-js'`);

      }
    });
  }
}

function makeInvalidEarlyAccess(name) {
  return () => assert(false, `call to '${name}' via reference taken before Wasm module initialization`);

}

function ignoredModuleProp(prop) {
  if (Object.getOwnPropertyDescriptor(Module, prop)) {
    abort(`\`Module.${prop}\` was supplied but \`${prop}\` not included in INCOMING_MODULE_JS_API`);
  }
}

// forcing the filesystem exports a few things by default
function isExportedByForceFilesystem(name) {
  return name === 'FS_createPath' ||
         name === 'FS_createDataFile' ||
         name === 'FS_createPreloadedFile' ||
         name === 'FS_preloadFile' ||
         name === 'FS_unlink' ||
         name === 'addRunDependency' ||
         // The old FS has some functionality that WasmFS lacks.
         name === 'FS_createLazyFile' ||
         name === 'FS_createDevice' ||
         name === 'removeRunDependency';
}

function missingLibrarySymbol(sym) {

  // Any symbol that is not included from the JS library is also (by definition)
  // not exported on the Module object.
  unexportedRuntimeSymbol(sym);
}

function unexportedRuntimeSymbol(sym) {
  if (!Object.getOwnPropertyDescriptor(Module, sym)) {
    Object.defineProperty(Module, sym, {
      configurable: true,
      get() {
        var msg = `'${sym}' was not exported. add it to EXPORTED_RUNTIME_METHODS (see the Emscripten FAQ)`;
        if (isExportedByForceFilesystem(sym)) {
          msg += '. Alternatively, forcing filesystem support (-sFORCE_FILESYSTEM) can export this for you';
        }
        abort(msg);
      },
    });
  }
}

// end include: runtime_debug.js
var readyPromiseResolve, readyPromiseReject;

// Memory management
var
/** @type {!Int8Array} */
  HEAP8,
/** @type {!Uint8Array} */
  HEAPU8,
/** @type {!Int16Array} */
  HEAP16,
/** @type {!Uint16Array} */
  HEAPU16,
/** @type {!Int32Array} */
  HEAP32,
/** @type {!Uint32Array} */
  HEAPU32,
/** @type {!Float32Array} */
  HEAPF32,
/** @type {!Float64Array} */
  HEAPF64;

// BigInt64Array type is not correctly defined in closure
var
/** not-@type {!BigInt64Array} */
  HEAP64,
/* BigUint64Array type is not correctly defined in closure
/** not-@type {!BigUint64Array} */
  HEAPU64;

var runtimeInitialized = false;



function updateMemoryViews() {
  var b = wasmMemory.buffer;
  HEAP8 = new Int8Array(b);
  HEAP16 = new Int16Array(b);
  HEAPU8 = new Uint8Array(b);
  HEAPU16 = new Uint16Array(b);
  HEAP32 = new Int32Array(b);
  HEAPU32 = new Uint32Array(b);
  HEAPF32 = new Float32Array(b);
  HEAPF64 = new Float64Array(b);
  HEAP64 = new BigInt64Array(b);
  HEAPU64 = new BigUint64Array(b);
}

// include: memoryprofiler.js
// end include: memoryprofiler.js
// end include: runtime_common.js
assert(globalThis.Int32Array && globalThis.Float64Array && Int32Array.prototype.subarray && Int32Array.prototype.set,
       'JS engine does not provide full typed array support');

function preRun() {
  if (Module['preRun']) {
    if (typeof Module['preRun'] == 'function') Module['preRun'] = [Module['preRun']];
    while (Module['preRun'].length) {
      addOnPreRun(Module['preRun'].shift());
    }
  }
  consumedModuleProp('preRun');
  // Begin ATPRERUNS hooks
  callRuntimeCallbacks(onPreRuns);
  // End ATPRERUNS hooks
}

function initRuntime() {
  assert(!runtimeInitialized);
  runtimeInitialized = true;

  checkStackCookie();

  // Begin ATINITS hooks
  if (!Module['noFSInit'] && !FS.initialized) FS.init();
TTY.init();
  // End ATINITS hooks

  wasmExports['__wasm_call_ctors']();

  // Begin ATPOSTCTORS hooks
  FS.ignorePermissions = false;
  // End ATPOSTCTORS hooks
}

function postRun() {
  checkStackCookie();
   // PThreads reuse the runtime from the main thread.

  if (Module['postRun']) {
    if (typeof Module['postRun'] == 'function') Module['postRun'] = [Module['postRun']];
    while (Module['postRun'].length) {
      addOnPostRun(Module['postRun'].shift());
    }
  }
  consumedModuleProp('postRun');

  // Begin ATPOSTRUNS hooks
  callRuntimeCallbacks(onPostRuns);
  // End ATPOSTRUNS hooks
}

/** @param {string|number=} what */
function abort(what) {
  Module['onAbort']?.(what);

  what = 'Aborted(' + what + ')';
  // TODO(sbc): Should we remove printing and leave it up to whoever
  // catches the exception?
  err(what);

  ABORT = true;

  // Use a wasm runtime error, because a JS error might be seen as a foreign
  // exception, which means we'd run destructors on it. We need the error to
  // simply make the program stop.
  // FIXME This approach does not work in Wasm EH because it currently does not assume
  // all RuntimeErrors are from traps; it decides whether a RuntimeError is from
  // a trap or not based on a hidden field within the object. So at the moment
  // we don't have a way of throwing a wasm trap from JS. TODO Make a JS API that
  // allows this in the wasm spec.

  // Suppress closure compiler warning here. Closure compiler's builtin extern
  // definition for WebAssembly.RuntimeError claims it takes no arguments even
  // though it can.
  // TODO(https://github.com/google/closure-compiler/pull/3913): Remove if/when upstream closure gets fixed.
  /** @suppress {checkTypes} */
  var e = new WebAssembly.RuntimeError(what);

  readyPromiseReject?.(e);
  // Throw the error whether or not MODULARIZE is set because abort is used
  // in code paths apart from instantiation where an exception is expected
  // to be thrown when abort is called.
  throw e;
}

function createExportWrapper(name, nargs) {
  return (...args) => {
    assert(runtimeInitialized, `native function \`${name}\` called before runtime initialization`);
    var f = wasmExports[name];
    assert(f, `exported native function \`${name}\` not found`);
    // Only assert for too many arguments. Too few can be valid since the missing arguments will be zero filled.
    assert(args.length <= nargs, `native function \`${name}\` called with ${args.length} args but expects ${nargs}`);
    return f(...args);
  };
}

var wasmBinaryFile;

function findWasmBinary() {

  if (Module['locateFile']) {
    return locateFile('libclang.wasm');
  }

  // Use bundler-friendly `new URL(..., import.meta.url)` pattern; works in browsers too.
  return new URL('libclang.wasm', import.meta.url).href;

}

function getBinarySync(file) {
  if (file == wasmBinaryFile && wasmBinary) {
    return new Uint8Array(wasmBinary);
  }
  if (readBinary) {
    return readBinary(file);
  }
  // Throwing a plain string here, even though it not normally adviables since
  // this gets turning into an `abort` in instantiateArrayBuffer.
  throw 'both async and sync fetching of the wasm failed';
}

async function getWasmBinary(binaryFile) {
  // If we don't have the binary yet, load it asynchronously using readAsync.
  if (!wasmBinary) {
    // Fetch the binary using readAsync
    try {
      var response = await readAsync(binaryFile);
      return new Uint8Array(response);
    } catch {
      // Fall back to getBinarySync below;
    }
  }

  // Otherwise, getBinarySync should be able to get it synchronously
  return getBinarySync(binaryFile);
}

async function instantiateArrayBuffer(binaryFile, imports) {
  try {
    var binary = await getWasmBinary(binaryFile);
    var instance = await WebAssembly.instantiate(binary, imports);
    return instance;
  } catch (reason) {
    err(`failed to asynchronously prepare wasm: ${reason}`);

    // Warn on some common problems.
    if (isFileURI(binaryFile)) {
      err(`warning: Loading from a file URI (${binaryFile}) is not supported in most browsers. See https://emscripten.org/docs/getting_started/FAQ.html#how-do-i-run-a-local-webserver-for-testing-why-does-my-program-stall-in-downloading-or-preparing`);
    }
    abort(reason);
  }
}

async function instantiateAsync(binary, binaryFile, imports) {
  if (!binary
      // Don't use streaming for file:// delivered objects in a webview, fetch them synchronously.
      && !isFileURI(binaryFile)
      // Avoid instantiateStreaming() on Node.js environment for now, as while
      // Node.js v18.1.0 implements it, it does not have a full fetch()
      // implementation yet.
      //
      // Reference:
      //   https://github.com/emscripten-core/emscripten/pull/16917
      && !ENVIRONMENT_IS_NODE
     ) {
    try {
      var response = fetch(binaryFile, { credentials: 'same-origin' });
      var instantiationResult = await WebAssembly.instantiateStreaming(response, imports);
      return instantiationResult;
    } catch (reason) {
      // We expect the most common failure cause to be a bad MIME type for the binary,
      // in which case falling back to ArrayBuffer instantiation should work.
      err(`wasm streaming compile failed: ${reason}`);
      err('falling back to ArrayBuffer instantiation');
      // fall back of instantiateArrayBuffer below
    };
  }
  return instantiateArrayBuffer(binaryFile, imports);
}

function getWasmImports() {
  // prepare imports
  var imports = {
    'env': wasmImports,
    'wasi_snapshot_preview1': wasmImports,
  };
  return imports;
}

// Create the wasm instance.
// Receives the wasm imports, returns the exports.
async function createWasm() {
  // Load the wasm module and create an instance of using native support in the JS engine.
  // handle a generated wasm instance, receiving its exports and
  // performing other necessary setup
  /** @param {WebAssembly.Module=} module*/
  function receiveInstance(instance, module) {
    wasmExports = instance.exports;

    assignWasmExports(wasmExports);

    Module['wasmExports'] = wasmExports;

    updateMemoryViews();

    return wasmExports;
  }

  // Prefer streaming instantiation if available.
  // Async compilation can be confusing when an error on the page overwrites Module
  // (for example, if the order of elements is wrong, and the one defining Module is
  // later), so we save Module and check it later.
  var trueModule = Module;
  function receiveInstantiationResult(result) {
    // 'result' is a ResultObject object which has both the module and instance.
    // receiveInstance() will swap in the exports (to Module.asm) so they can be called
    assert(Module === trueModule, 'the Module object should not be replaced during async compilation - perhaps the order of HTML elements is wrong?');
    trueModule = null;
    // TODO: Due to Closure regression https://github.com/google/closure-compiler/issues/3193, the above line no longer optimizes out down to the following line.
    // When the regression is fixed, can restore the above PTHREADS-enabled path.
    return receiveInstance(result['instance']);
  }

  var info = getWasmImports();

  // User shell pages can write their own Module.instantiateWasm = function(imports, successCallback) callback
  // to manually instantiate the Wasm module themselves. This allows pages to
  // run the instantiation parallel to any other async startup actions they are
  // performing.
  // Also pthreads and wasm workers initialize the wasm instance through this
  // path.
  if (Module['instantiateWasm']) {
    return new Promise((resolve, reject) => {
      try {
        Module['instantiateWasm'](info, (inst, mod) => {
          resolve(receiveInstance(inst, mod));
        });
      } catch(e) {
        err(`Module.instantiateWasm callback failed with error: ${e}`);
        reject(e);
      }
    });
  }

  wasmBinaryFile ??= findWasmBinary();
  var result = await instantiateAsync(wasmBinary, wasmBinaryFile, info);
  var exports = receiveInstantiationResult(result);
  return exports;
}

// end include: preamble.js

// Begin JS library code


  class ExitStatus {
      name = 'ExitStatus';
      constructor(status) {
        this.message = `Program terminated with exit(${status})`;
        this.status = status;
      }
    }

  var callRuntimeCallbacks = (callbacks) => {
      while (callbacks.length > 0) {
        // Pass the module as the first argument.
        callbacks.shift()(Module);
      }
    };
  var onPostRuns = [];
  var addOnPostRun = (cb) => onPostRuns.push(cb);

  var onPreRuns = [];
  var addOnPreRun = (cb) => onPreRuns.push(cb);


  
    /**
     * @param {number} ptr
     * @param {string} type
     */
  function getValue(ptr, type = 'i8') {
    if (type.endsWith('*')) type = '*';
    switch (type) {
      case 'i1': return HEAP8[ptr];
      case 'i8': return HEAP8[ptr];
      case 'i16': return HEAP16[((ptr)>>1)];
      case 'i32': return HEAP32[((ptr)>>2)];
      case 'i64': return HEAP64[((ptr)>>3)];
      case 'float': return HEAPF32[((ptr)>>2)];
      case 'double': return HEAPF64[((ptr)>>3)];
      case '*': return HEAPU32[((ptr)>>2)];
      default: abort(`invalid type for getValue: ${type}`);
    }
  }

  var noExitRuntime = true;

  var ptrToString = (ptr) => {
      assert(typeof ptr === 'number', `ptrToString expects a number, got ${typeof ptr}`);
      // Convert to 32-bit unsigned value
      ptr >>>= 0;
      return '0x' + ptr.toString(16).padStart(8, '0');
    };

  
    /**
     * @param {number} ptr
     * @param {number} value
     * @param {string} type
     */
  function setValue(ptr, value, type = 'i8') {
    if (type.endsWith('*')) type = '*';
    switch (type) {
      case 'i1': HEAP8[ptr] = value; break;
      case 'i8': HEAP8[ptr] = value; break;
      case 'i16': HEAP16[((ptr)>>1)] = value; break;
      case 'i32': HEAP32[((ptr)>>2)] = value; break;
      case 'i64': HEAP64[((ptr)>>3)] = BigInt(value); break;
      case 'float': HEAPF32[((ptr)>>2)] = value; break;
      case 'double': HEAPF64[((ptr)>>3)] = value; break;
      case '*': HEAPU32[((ptr)>>2)] = value; break;
      default: abort(`invalid type for setValue: ${type}`);
    }
  }

  var stackRestore = (val) => __emscripten_stack_restore(val);

  var stackSave = () => _emscripten_stack_get_current();

  var warnOnce = (text) => {
      warnOnce.shown ||= {};
      if (!warnOnce.shown[text]) {
        warnOnce.shown[text] = 1;
        if (ENVIRONMENT_IS_NODE) text = 'warning: ' + text;
        err(text);
      }
    };

  

  var wasmTableMirror = [];
  
  
  var getWasmTableEntry = (funcPtr) => {
      var func = wasmTableMirror[funcPtr];
      if (!func) {
        /** @suppress {checkTypes} */
        wasmTableMirror[funcPtr] = func = wasmTable.get(funcPtr);
      }
      /** @suppress {checkTypes} */
      assert(wasmTable.get(funcPtr) == func, 'JavaScript-side Wasm function table mirror is out of date!');
      return func;
    };
  var ___call_sighandler = (fp, sig) => getWasmTableEntry(fp)(sig);

  class ExceptionInfo {
      // excPtr - Thrown object pointer to wrap. Metadata pointer is calculated from it.
      constructor(excPtr) {
        this.excPtr = excPtr;
        this.ptr = excPtr - 24;
      }
  
      set_type(type) {
        HEAPU32[(((this.ptr)+(4))>>2)] = type;
      }
  
      get_type() {
        return HEAPU32[(((this.ptr)+(4))>>2)];
      }
  
      set_destructor(destructor) {
        HEAPU32[(((this.ptr)+(8))>>2)] = destructor;
      }
  
      get_destructor() {
        return HEAPU32[(((this.ptr)+(8))>>2)];
      }
  
      set_caught(caught) {
        caught = caught ? 1 : 0;
        HEAP8[(this.ptr)+(12)] = caught;
      }
  
      get_caught() {
        return HEAP8[(this.ptr)+(12)] != 0;
      }
  
      set_rethrown(rethrown) {
        rethrown = rethrown ? 1 : 0;
        HEAP8[(this.ptr)+(13)] = rethrown;
      }
  
      get_rethrown() {
        return HEAP8[(this.ptr)+(13)] != 0;
      }
  
      // Initialize native structure fields. Should be called once after allocated.
      init(type, destructor) {
        this.set_adjusted_ptr(0);
        this.set_type(type);
        this.set_destructor(destructor);
      }
  
      set_adjusted_ptr(adjustedPtr) {
        HEAPU32[(((this.ptr)+(16))>>2)] = adjustedPtr;
      }
  
      get_adjusted_ptr() {
        return HEAPU32[(((this.ptr)+(16))>>2)];
      }
    }
  
  var exceptionLast = 0;
  
  var uncaughtExceptionCount = 0;
  var ___cxa_throw = (ptr, type, destructor) => {
      var info = new ExceptionInfo(ptr);
      // Initialize ExceptionInfo content after it was allocated in __cxa_allocate_exception.
      info.init(type, destructor);
      exceptionLast = ptr;
      uncaughtExceptionCount++;
      assert(false, 'Exception thrown, but exception catching is not enabled. Compile with -sNO_DISABLE_EXCEPTION_CATCHING or -sEXCEPTION_CATCHING_ALLOWED=[..] to catch.');
    };

  var PATH = {
  isAbs:(path) => path.charAt(0) === '/',
  splitPath:(filename) => {
        var splitPathRe = /^(\/?|)([\s\S]*?)((?:\.{1,2}|[^\/]+?|)(\.[^.\/]*|))(?:[\/]*)$/;
        return splitPathRe.exec(filename).slice(1);
      },
  normalizeArray:(parts, allowAboveRoot) => {
        // if the path tries to go above the root, `up` ends up > 0
        var up = 0;
        for (var i = parts.length - 1; i >= 0; i--) {
          var last = parts[i];
          if (last === '.') {
            parts.splice(i, 1);
          } else if (last === '..') {
            parts.splice(i, 1);
            up++;
          } else if (up) {
            parts.splice(i, 1);
            up--;
          }
        }
        // if the path is allowed to go above the root, restore leading ..s
        if (allowAboveRoot) {
          for (; up; up--) {
            parts.unshift('..');
          }
        }
        return parts;
      },
  normalize:(path) => {
        var isAbsolute = PATH.isAbs(path),
            trailingSlash = path.slice(-1) === '/';
        // Normalize the path
        path = PATH.normalizeArray(path.split('/').filter((p) => !!p), !isAbsolute).join('/');
        if (!path && !isAbsolute) {
          path = '.';
        }
        if (path && trailingSlash) {
          path += '/';
        }
        return (isAbsolute ? '/' : '') + path;
      },
  dirname:(path) => {
        var result = PATH.splitPath(path),
            root = result[0],
            dir = result[1];
        if (!root && !dir) {
          // No dirname whatsoever
          return '.';
        }
        if (dir) {
          // It has a dirname, strip trailing slash
          dir = dir.slice(0, -1);
        }
        return root + dir;
      },
  basename:(path) => path && path.match(/([^\/]+|\/)\/*$/)[1],
  join:(...paths) => PATH.normalize(paths.join('/')),
  join2:(l, r) => PATH.normalize(l + '/' + r),
  };
  
  var initRandomFill = () => {
      // This block is not needed on v19+ since crypto.getRandomValues is builtin
      if (ENVIRONMENT_IS_NODE) {
        var nodeCrypto = require('crypto');
        return (view) => nodeCrypto.randomFillSync(view);
      }
  
      return (view) => crypto.getRandomValues(view);
    };
  var randomFill = (view) => {
      // Lazily init on the first invocation.
      (randomFill = initRandomFill())(view);
    };
  
  
  
  var PATH_FS = {
  resolve:(...args) => {
        var resolvedPath = '',
          resolvedAbsolute = false;
        for (var i = args.length - 1; i >= -1 && !resolvedAbsolute; i--) {
          var path = (i >= 0) ? args[i] : FS.cwd();
          // Skip empty and invalid entries
          if (typeof path != 'string') {
            throw new TypeError('Arguments to path.resolve must be strings');
          } else if (!path) {
            return ''; // an invalid portion invalidates the whole thing
          }
          resolvedPath = path + '/' + resolvedPath;
          resolvedAbsolute = PATH.isAbs(path);
        }
        // At this point the path should be resolved to a full absolute path, but
        // handle relative paths to be safe (might happen when process.cwd() fails)
        resolvedPath = PATH.normalizeArray(resolvedPath.split('/').filter((p) => !!p), !resolvedAbsolute).join('/');
        return ((resolvedAbsolute ? '/' : '') + resolvedPath) || '.';
      },
  relative:(from, to) => {
        from = PATH_FS.resolve(from).slice(1);
        to = PATH_FS.resolve(to).slice(1);
        function trim(arr) {
          var start = 0;
          for (; start < arr.length; start++) {
            if (arr[start] !== '') break;
          }
          var end = arr.length - 1;
          for (; end >= 0; end--) {
            if (arr[end] !== '') break;
          }
          if (start > end) return [];
          return arr.slice(start, end - start + 1);
        }
        var fromParts = trim(from.split('/'));
        var toParts = trim(to.split('/'));
        var length = Math.min(fromParts.length, toParts.length);
        var samePartsLength = length;
        for (var i = 0; i < length; i++) {
          if (fromParts[i] !== toParts[i]) {
            samePartsLength = i;
            break;
          }
        }
        var outputParts = [];
        for (var i = samePartsLength; i < fromParts.length; i++) {
          outputParts.push('..');
        }
        outputParts = outputParts.concat(toParts.slice(samePartsLength));
        return outputParts.join('/');
      },
  };
  
  
  var UTF8Decoder = globalThis.TextDecoder && new TextDecoder();
  
  var findStringEnd = (heapOrArray, idx, maxBytesToRead, ignoreNul) => {
      var maxIdx = idx + maxBytesToRead;
      if (ignoreNul) return maxIdx;
      // TextDecoder needs to know the byte length in advance, it doesn't stop on
      // null terminator by itself.
      // As a tiny code save trick, compare idx against maxIdx using a negation,
      // so that maxBytesToRead=undefined/NaN means Infinity.
      while (heapOrArray[idx] && !(idx >= maxIdx)) ++idx;
      return idx;
    };
  
  
    /**
     * Given a pointer 'idx' to a null-terminated UTF8-encoded string in the given
     * array that contains uint8 values, returns a copy of that string as a
     * Javascript String object.
     * heapOrArray is either a regular array, or a JavaScript typed array view.
     * @param {number=} idx
     * @param {number=} maxBytesToRead
     * @param {boolean=} ignoreNul - If true, the function will not stop on a NUL character.
     * @return {string}
     */
  var UTF8ArrayToString = (heapOrArray, idx = 0, maxBytesToRead, ignoreNul) => {
  
      var endPtr = findStringEnd(heapOrArray, idx, maxBytesToRead, ignoreNul);
  
      // When using conditional TextDecoder, skip it for short strings as the overhead of the native call is not worth it.
      if (endPtr - idx > 16 && heapOrArray.buffer && UTF8Decoder) {
        return UTF8Decoder.decode(heapOrArray.subarray(idx, endPtr));
      }
      var str = '';
      while (idx < endPtr) {
        // For UTF8 byte structure, see:
        // http://en.wikipedia.org/wiki/UTF-8#Description
        // https://www.ietf.org/rfc/rfc2279.txt
        // https://tools.ietf.org/html/rfc3629
        var u0 = heapOrArray[idx++];
        if (!(u0 & 0x80)) { str += String.fromCharCode(u0); continue; }
        var u1 = heapOrArray[idx++] & 63;
        if ((u0 & 0xE0) == 0xC0) { str += String.fromCharCode(((u0 & 31) << 6) | u1); continue; }
        var u2 = heapOrArray[idx++] & 63;
        if ((u0 & 0xF0) == 0xE0) {
          u0 = ((u0 & 15) << 12) | (u1 << 6) | u2;
        } else {
          if ((u0 & 0xF8) != 0xF0) warnOnce('Invalid UTF-8 leading byte ' + ptrToString(u0) + ' encountered when deserializing a UTF-8 string in wasm memory to a JS string!');
          u0 = ((u0 & 7) << 18) | (u1 << 12) | (u2 << 6) | (heapOrArray[idx++] & 63);
        }
  
        if (u0 < 0x10000) {
          str += String.fromCharCode(u0);
        } else {
          var ch = u0 - 0x10000;
          str += String.fromCharCode(0xD800 | (ch >> 10), 0xDC00 | (ch & 0x3FF));
        }
      }
      return str;
    };
  
  var FS_stdin_getChar_buffer = [];
  
  var lengthBytesUTF8 = (str) => {
      var len = 0;
      for (var i = 0; i < str.length; ++i) {
        // Gotcha: charCodeAt returns a 16-bit word that is a UTF-16 encoded code
        // unit, not a Unicode code point of the character! So decode
        // UTF16->UTF32->UTF8.
        // See http://unicode.org/faq/utf_bom.html#utf16-3
        var c = str.charCodeAt(i); // possibly a lead surrogate
        if (c <= 0x7F) {
          len++;
        } else if (c <= 0x7FF) {
          len += 2;
        } else if (c >= 0xD800 && c <= 0xDFFF) {
          len += 4; ++i;
        } else {
          len += 3;
        }
      }
      return len;
    };
  
  var stringToUTF8Array = (str, heap, outIdx, maxBytesToWrite) => {
      assert(typeof str === 'string', `stringToUTF8Array expects a string (got ${typeof str})`);
      // Parameter maxBytesToWrite is not optional. Negative values, 0, null,
      // undefined and false each don't write out any bytes.
      if (!(maxBytesToWrite > 0))
        return 0;
  
      var startIdx = outIdx;
      var endIdx = outIdx + maxBytesToWrite - 1; // -1 for string null terminator.
      for (var i = 0; i < str.length; ++i) {
        // For UTF8 byte structure, see http://en.wikipedia.org/wiki/UTF-8#Description
        // and https://www.ietf.org/rfc/rfc2279.txt
        // and https://tools.ietf.org/html/rfc3629
        var u = str.codePointAt(i);
        if (u <= 0x7F) {
          if (outIdx >= endIdx) break;
          heap[outIdx++] = u;
        } else if (u <= 0x7FF) {
          if (outIdx + 1 >= endIdx) break;
          heap[outIdx++] = 0xC0 | (u >> 6);
          heap[outIdx++] = 0x80 | (u & 63);
        } else if (u <= 0xFFFF) {
          if (outIdx + 2 >= endIdx) break;
          heap[outIdx++] = 0xE0 | (u >> 12);
          heap[outIdx++] = 0x80 | ((u >> 6) & 63);
          heap[outIdx++] = 0x80 | (u & 63);
        } else {
          if (outIdx + 3 >= endIdx) break;
          if (u > 0x10FFFF) warnOnce('Invalid Unicode code point ' + ptrToString(u) + ' encountered when serializing a JS string to a UTF-8 string in wasm memory! (Valid unicode code points should be in range 0-0x10FFFF).');
          heap[outIdx++] = 0xF0 | (u >> 18);
          heap[outIdx++] = 0x80 | ((u >> 12) & 63);
          heap[outIdx++] = 0x80 | ((u >> 6) & 63);
          heap[outIdx++] = 0x80 | (u & 63);
          // Gotcha: if codePoint is over 0xFFFF, it is represented as a surrogate pair in UTF-16.
          // We need to manually skip over the second code unit for correct iteration.
          i++;
        }
      }
      // Null-terminate the pointer to the buffer.
      heap[outIdx] = 0;
      return outIdx - startIdx;
    };
  /** @type {function(string, boolean=, number=)} */
  var intArrayFromString = (stringy, dontAddNull, length) => {
      var len = length > 0 ? length : lengthBytesUTF8(stringy)+1;
      var u8array = new Array(len);
      var numBytesWritten = stringToUTF8Array(stringy, u8array, 0, u8array.length);
      if (dontAddNull) u8array.length = numBytesWritten;
      return u8array;
    };
  var FS_stdin_getChar = () => {
      if (!FS_stdin_getChar_buffer.length) {
        var result = null;
        if (ENVIRONMENT_IS_NODE) {
          // we will read data by chunks of BUFSIZE
          var BUFSIZE = 256;
          var buf = Buffer.alloc(BUFSIZE);
          var bytesRead = 0;
  
          // For some reason we must suppress a closure warning here, even though
          // fd definitely exists on process.stdin, and is even the proper way to
          // get the fd of stdin,
          // https://github.com/nodejs/help/issues/2136#issuecomment-523649904
          // This started to happen after moving this logic out of library_tty.js,
          // so it is related to the surrounding code in some unclear manner.
          /** @suppress {missingProperties} */
          var fd = process.stdin.fd;
  
          try {
            bytesRead = fs.readSync(fd, buf, 0, BUFSIZE);
          } catch(e) {
            // Cross-platform differences: on Windows, reading EOF throws an
            // exception, but on other OSes, reading EOF returns 0. Uniformize
            // behavior by treating the EOF exception to return 0.
            if (e.toString().includes('EOF')) bytesRead = 0;
            else throw e;
          }
  
          if (bytesRead > 0) {
            result = buf.slice(0, bytesRead).toString('utf-8');
          }
        } else
        if (globalThis.window?.prompt) {
          // Browser.
          result = window.prompt('Input: ');  // returns null on cancel
          if (result !== null) {
            result += '\n';
          }
        } else
        {}
        if (!result) {
          return null;
        }
        FS_stdin_getChar_buffer = intArrayFromString(result, true);
      }
      return FS_stdin_getChar_buffer.shift();
    };
  var TTY = {
  ttys:[],
  init() {
        // https://github.com/emscripten-core/emscripten/pull/1555
        // if (ENVIRONMENT_IS_NODE) {
        //   // currently, FS.init does not distinguish if process.stdin is a file or TTY
        //   // device, it always assumes it's a TTY device. because of this, we're forcing
        //   // process.stdin to UTF8 encoding to at least make stdin reading compatible
        //   // with text files until FS.init can be refactored.
        //   process.stdin.setEncoding('utf8');
        // }
      },
  shutdown() {
        // https://github.com/emscripten-core/emscripten/pull/1555
        // if (ENVIRONMENT_IS_NODE) {
        //   // inolen: any idea as to why node -e 'process.stdin.read()' wouldn't exit immediately (with process.stdin being a tty)?
        //   // isaacs: because now it's reading from the stream, you've expressed interest in it, so that read() kicks off a _read() which creates a ReadReq operation
        //   // inolen: I thought read() in that case was a synchronous operation that just grabbed some amount of buffered data if it exists?
        //   // isaacs: it is. but it also triggers a _read() call, which calls readStart() on the handle
        //   // isaacs: do process.stdin.pause() and i'd think it'd probably close the pending call
        //   process.stdin.pause();
        // }
      },
  register(dev, ops) {
        TTY.ttys[dev] = { input: [], output: [], ops: ops };
        FS.registerDevice(dev, TTY.stream_ops);
      },
  stream_ops:{
  open(stream) {
          var tty = TTY.ttys[stream.node.rdev];
          if (!tty) {
            throw new FS.ErrnoError(43);
          }
          stream.tty = tty;
          stream.seekable = false;
        },
  close(stream) {
          // flush any pending line data
          stream.tty.ops.fsync(stream.tty);
        },
  fsync(stream) {
          stream.tty.ops.fsync(stream.tty);
        },
  read(stream, buffer, offset, length, pos /* ignored */) {
          if (!stream.tty || !stream.tty.ops.get_char) {
            throw new FS.ErrnoError(60);
          }
          var bytesRead = 0;
          for (var i = 0; i < length; i++) {
            var result;
            try {
              result = stream.tty.ops.get_char(stream.tty);
            } catch (e) {
              throw new FS.ErrnoError(29);
            }
            if (result === undefined && bytesRead === 0) {
              throw new FS.ErrnoError(6);
            }
            if (result === null || result === undefined) break;
            bytesRead++;
            buffer[offset+i] = result;
          }
          if (bytesRead) {
            stream.node.atime = Date.now();
          }
          return bytesRead;
        },
  write(stream, buffer, offset, length, pos) {
          if (!stream.tty || !stream.tty.ops.put_char) {
            throw new FS.ErrnoError(60);
          }
          try {
            for (var i = 0; i < length; i++) {
              stream.tty.ops.put_char(stream.tty, buffer[offset+i]);
            }
          } catch (e) {
            throw new FS.ErrnoError(29);
          }
          if (length) {
            stream.node.mtime = stream.node.ctime = Date.now();
          }
          return i;
        },
  },
  default_tty_ops:{
  get_char(tty) {
          return FS_stdin_getChar();
        },
  put_char(tty, val) {
          if (val === null || val === 10) {
            out(UTF8ArrayToString(tty.output));
            tty.output = [];
          } else {
            if (val != 0) tty.output.push(val); // val == 0 would cut text output off in the middle.
          }
        },
  fsync(tty) {
          if (tty.output?.length > 0) {
            out(UTF8ArrayToString(tty.output));
            tty.output = [];
          }
        },
  ioctl_tcgets(tty) {
          // typical setting
          return {
            c_iflag: 25856,
            c_oflag: 5,
            c_cflag: 191,
            c_lflag: 35387,
            c_cc: [
              0x03, 0x1c, 0x7f, 0x15, 0x04, 0x00, 0x01, 0x00, 0x11, 0x13, 0x1a, 0x00,
              0x12, 0x0f, 0x17, 0x16, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
              0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            ]
          };
        },
  ioctl_tcsets(tty, optional_actions, data) {
          // currently just ignore
          return 0;
        },
  ioctl_tiocgwinsz(tty) {
          return [24, 80];
        },
  },
  default_tty1_ops:{
  put_char(tty, val) {
          if (val === null || val === 10) {
            err(UTF8ArrayToString(tty.output));
            tty.output = [];
          } else {
            if (val != 0) tty.output.push(val);
          }
        },
  fsync(tty) {
          if (tty.output?.length > 0) {
            err(UTF8ArrayToString(tty.output));
            tty.output = [];
          }
        },
  },
  };
  
  
  var zeroMemory = (ptr, size) => HEAPU8.fill(0, ptr, ptr + size);
  
  var alignMemory = (size, alignment) => {
      assert(alignment, "alignment argument is required");
      return Math.ceil(size / alignment) * alignment;
    };
  var mmapAlloc = (size) => {
      size = alignMemory(size, 65536);
      var ptr = _emscripten_builtin_memalign(65536, size);
      if (ptr) zeroMemory(ptr, size);
      return ptr;
    };
  var MEMFS = {
  ops_table:null,
  mount(mount) {
        return MEMFS.createNode(null, '/', 16895, 0);
      },
  createNode(parent, name, mode, dev) {
        if (FS.isBlkdev(mode) || FS.isFIFO(mode)) {
          // no supported
          throw new FS.ErrnoError(63);
        }
        MEMFS.ops_table ||= {
          dir: {
            node: {
              getattr: MEMFS.node_ops.getattr,
              setattr: MEMFS.node_ops.setattr,
              lookup: MEMFS.node_ops.lookup,
              mknod: MEMFS.node_ops.mknod,
              rename: MEMFS.node_ops.rename,
              unlink: MEMFS.node_ops.unlink,
              rmdir: MEMFS.node_ops.rmdir,
              readdir: MEMFS.node_ops.readdir,
              symlink: MEMFS.node_ops.symlink
            },
            stream: {
              llseek: MEMFS.stream_ops.llseek
            }
          },
          file: {
            node: {
              getattr: MEMFS.node_ops.getattr,
              setattr: MEMFS.node_ops.setattr
            },
            stream: {
              llseek: MEMFS.stream_ops.llseek,
              read: MEMFS.stream_ops.read,
              write: MEMFS.stream_ops.write,
              mmap: MEMFS.stream_ops.mmap,
              msync: MEMFS.stream_ops.msync
            }
          },
          link: {
            node: {
              getattr: MEMFS.node_ops.getattr,
              setattr: MEMFS.node_ops.setattr,
              readlink: MEMFS.node_ops.readlink
            },
            stream: {}
          },
          chrdev: {
            node: {
              getattr: MEMFS.node_ops.getattr,
              setattr: MEMFS.node_ops.setattr
            },
            stream: FS.chrdev_stream_ops
          }
        };
        var node = FS.createNode(parent, name, mode, dev);
        if (FS.isDir(node.mode)) {
          node.node_ops = MEMFS.ops_table.dir.node;
          node.stream_ops = MEMFS.ops_table.dir.stream;
          node.contents = {};
        } else if (FS.isFile(node.mode)) {
          node.node_ops = MEMFS.ops_table.file.node;
          node.stream_ops = MEMFS.ops_table.file.stream;
          node.usedBytes = 0; // The actual number of bytes used in the typed array, as opposed to contents.length which gives the whole capacity.
          // When the byte data of the file is populated, this will point to either a typed array, or a normal JS array. Typed arrays are preferred
          // for performance, and used by default. However, typed arrays are not resizable like normal JS arrays are, so there is a small disk size
          // penalty involved for appending file writes that continuously grow a file similar to std::vector capacity vs used -scheme.
          node.contents = null; 
        } else if (FS.isLink(node.mode)) {
          node.node_ops = MEMFS.ops_table.link.node;
          node.stream_ops = MEMFS.ops_table.link.stream;
        } else if (FS.isChrdev(node.mode)) {
          node.node_ops = MEMFS.ops_table.chrdev.node;
          node.stream_ops = MEMFS.ops_table.chrdev.stream;
        }
        node.atime = node.mtime = node.ctime = Date.now();
        // add the new node to the parent
        if (parent) {
          parent.contents[name] = node;
          parent.atime = parent.mtime = parent.ctime = node.atime;
        }
        return node;
      },
  getFileDataAsTypedArray(node) {
        if (!node.contents) return new Uint8Array(0);
        if (node.contents.subarray) return node.contents.subarray(0, node.usedBytes); // Make sure to not return excess unused bytes.
        return new Uint8Array(node.contents);
      },
  expandFileStorage(node, newCapacity) {
        var prevCapacity = node.contents ? node.contents.length : 0;
        if (prevCapacity >= newCapacity) return; // No need to expand, the storage was already large enough.
        // Don't expand strictly to the given requested limit if it's only a very small increase, but instead geometrically grow capacity.
        // For small filesizes (<1MB), perform size*2 geometric increase, but for large sizes, do a much more conservative size*1.125 increase to
        // avoid overshooting the allocation cap by a very large margin.
        var CAPACITY_DOUBLING_MAX = 1024 * 1024;
        newCapacity = Math.max(newCapacity, (prevCapacity * (prevCapacity < CAPACITY_DOUBLING_MAX ? 2.0 : 1.125)) >>> 0);
        if (prevCapacity != 0) newCapacity = Math.max(newCapacity, 256); // At minimum allocate 256b for each file when expanding.
        var oldContents = node.contents;
        node.contents = new Uint8Array(newCapacity); // Allocate new storage.
        if (node.usedBytes > 0) node.contents.set(oldContents.subarray(0, node.usedBytes), 0); // Copy old data over to the new storage.
      },
  resizeFileStorage(node, newSize) {
        if (node.usedBytes == newSize) return;
        if (newSize == 0) {
          node.contents = null; // Fully decommit when requesting a resize to zero.
          node.usedBytes = 0;
        } else {
          var oldContents = node.contents;
          node.contents = new Uint8Array(newSize); // Allocate new storage.
          if (oldContents) {
            node.contents.set(oldContents.subarray(0, Math.min(newSize, node.usedBytes))); // Copy old data over to the new storage.
          }
          node.usedBytes = newSize;
        }
      },
  node_ops:{
  getattr(node) {
          var attr = {};
          // device numbers reuse inode numbers.
          attr.dev = FS.isChrdev(node.mode) ? node.id : 1;
          attr.ino = node.id;
          attr.mode = node.mode;
          attr.nlink = 1;
          attr.uid = 0;
          attr.gid = 0;
          attr.rdev = node.rdev;
          if (FS.isDir(node.mode)) {
            attr.size = 4096;
          } else if (FS.isFile(node.mode)) {
            attr.size = node.usedBytes;
          } else if (FS.isLink(node.mode)) {
            attr.size = node.link.length;
          } else {
            attr.size = 0;
          }
          attr.atime = new Date(node.atime);
          attr.mtime = new Date(node.mtime);
          attr.ctime = new Date(node.ctime);
          // NOTE: In our implementation, st_blocks = Math.ceil(st_size/st_blksize),
          //       but this is not required by the standard.
          attr.blksize = 4096;
          attr.blocks = Math.ceil(attr.size / attr.blksize);
          return attr;
        },
  setattr(node, attr) {
          for (const key of ["mode", "atime", "mtime", "ctime"]) {
            if (attr[key] != null) {
              node[key] = attr[key];
            }
          }
          if (attr.size !== undefined) {
            MEMFS.resizeFileStorage(node, attr.size);
          }
        },
  lookup(parent, name) {
          throw new FS.ErrnoError(44);
        },
  mknod(parent, name, mode, dev) {
          return MEMFS.createNode(parent, name, mode, dev);
        },
  rename(old_node, new_dir, new_name) {
          var new_node;
          try {
            new_node = FS.lookupNode(new_dir, new_name);
          } catch (e) {}
          if (new_node) {
            if (FS.isDir(old_node.mode)) {
              // if we're overwriting a directory at new_name, make sure it's empty.
              for (var i in new_node.contents) {
                throw new FS.ErrnoError(55);
              }
            }
            FS.hashRemoveNode(new_node);
          }
          // do the internal rewiring
          delete old_node.parent.contents[old_node.name];
          new_dir.contents[new_name] = old_node;
          old_node.name = new_name;
          new_dir.ctime = new_dir.mtime = old_node.parent.ctime = old_node.parent.mtime = Date.now();
        },
  unlink(parent, name) {
          delete parent.contents[name];
          parent.ctime = parent.mtime = Date.now();
        },
  rmdir(parent, name) {
          var node = FS.lookupNode(parent, name);
          for (var i in node.contents) {
            throw new FS.ErrnoError(55);
          }
          delete parent.contents[name];
          parent.ctime = parent.mtime = Date.now();
        },
  readdir(node) {
          return ['.', '..', ...Object.keys(node.contents)];
        },
  symlink(parent, newname, oldpath) {
          var node = MEMFS.createNode(parent, newname, 0o777 | 40960, 0);
          node.link = oldpath;
          return node;
        },
  readlink(node) {
          if (!FS.isLink(node.mode)) {
            throw new FS.ErrnoError(28);
          }
          return node.link;
        },
  },
  stream_ops:{
  read(stream, buffer, offset, length, position) {
          var contents = stream.node.contents;
          if (position >= stream.node.usedBytes) return 0;
          var size = Math.min(stream.node.usedBytes - position, length);
          assert(size >= 0);
          if (size > 8 && contents.subarray) { // non-trivial, and typed array
            buffer.set(contents.subarray(position, position + size), offset);
          } else {
            for (var i = 0; i < size; i++) buffer[offset + i] = contents[position + i];
          }
          return size;
        },
  write(stream, buffer, offset, length, position, canOwn) {
          // The data buffer should be a typed array view
          assert(!(buffer instanceof ArrayBuffer));
          // If the buffer is located in main memory (HEAP), and if
          // memory can grow, we can't hold on to references of the
          // memory buffer, as they may get invalidated. That means we
          // need to do copy its contents.
          if (buffer.buffer === HEAP8.buffer) {
            canOwn = false;
          }
  
          if (!length) return 0;
          var node = stream.node;
          node.mtime = node.ctime = Date.now();
  
          if (buffer.subarray && (!node.contents || node.contents.subarray)) { // This write is from a typed array to a typed array?
            if (canOwn) {
              assert(position === 0, 'canOwn must imply no weird position inside the file');
              node.contents = buffer.subarray(offset, offset + length);
              node.usedBytes = length;
              return length;
            } else if (node.usedBytes === 0 && position === 0) { // If this is a simple first write to an empty file, do a fast set since we don't need to care about old data.
              node.contents = buffer.slice(offset, offset + length);
              node.usedBytes = length;
              return length;
            } else if (position + length <= node.usedBytes) { // Writing to an already allocated and used subrange of the file?
              node.contents.set(buffer.subarray(offset, offset + length), position);
              return length;
            }
          }
  
          // Appending to an existing file and we need to reallocate, or source data did not come as a typed array.
          MEMFS.expandFileStorage(node, position+length);
          if (node.contents.subarray && buffer.subarray) {
            // Use typed array write which is available.
            node.contents.set(buffer.subarray(offset, offset + length), position);
          } else {
            for (var i = 0; i < length; i++) {
             node.contents[position + i] = buffer[offset + i]; // Or fall back to manual write if not.
            }
          }
          node.usedBytes = Math.max(node.usedBytes, position + length);
          return length;
        },
  llseek(stream, offset, whence) {
          var position = offset;
          if (whence === 1) {
            position += stream.position;
          } else if (whence === 2) {
            if (FS.isFile(stream.node.mode)) {
              position += stream.node.usedBytes;
            }
          }
          if (position < 0) {
            throw new FS.ErrnoError(28);
          }
          return position;
        },
  mmap(stream, length, position, prot, flags) {
          if (!FS.isFile(stream.node.mode)) {
            throw new FS.ErrnoError(43);
          }
          var ptr;
          var allocated;
          var contents = stream.node.contents;
          // Only make a new copy when MAP_PRIVATE is specified.
          if (!(flags & 2) && contents && contents.buffer === HEAP8.buffer) {
            // We can't emulate MAP_SHARED when the file is not backed by the
            // buffer we're mapping to (e.g. the HEAP buffer).
            allocated = false;
            ptr = contents.byteOffset;
          } else {
            allocated = true;
            ptr = mmapAlloc(length);
            if (!ptr) {
              throw new FS.ErrnoError(48);
            }
            if (contents) {
              // Try to avoid unnecessary slices.
              if (position > 0 || position + length < contents.length) {
                if (contents.subarray) {
                  contents = contents.subarray(position, position + length);
                } else {
                  contents = Array.prototype.slice.call(contents, position, position + length);
                }
              }
              HEAP8.set(contents, ptr);
            }
          }
          return { ptr, allocated };
        },
  msync(stream, buffer, offset, length, mmapFlags) {
          MEMFS.stream_ops.write(stream, buffer, 0, length, offset, false);
          // should we check if bytesWritten and length are the same?
          return 0;
        },
  },
  };
  
  var FS_modeStringToFlags = (str) => {
      var flagModes = {
        'r': 0,
        'r+': 2,
        'w': 512 | 64 | 1,
        'w+': 512 | 64 | 2,
        'a': 1024 | 64 | 1,
        'a+': 1024 | 64 | 2,
      };
      var flags = flagModes[str];
      if (typeof flags == 'undefined') {
        throw new Error(`Unknown file open mode: ${str}`);
      }
      return flags;
    };
  
  var FS_getMode = (canRead, canWrite) => {
      var mode = 0;
      if (canRead) mode |= 292 | 73;
      if (canWrite) mode |= 146;
      return mode;
    };
  
  
  
  
    /**
     * Given a pointer 'ptr' to a null-terminated UTF8-encoded string in the
     * emscripten HEAP, returns a copy of that string as a Javascript String object.
     *
     * @param {number} ptr
     * @param {number=} maxBytesToRead - An optional length that specifies the
     *   maximum number of bytes to read. You can omit this parameter to scan the
     *   string until the first 0 byte. If maxBytesToRead is passed, and the string
     *   at [ptr, ptr+maxBytesToReadr[ contains a null byte in the middle, then the
     *   string will cut short at that byte index.
     * @param {boolean=} ignoreNul - If true, the function will not stop on a NUL character.
     * @return {string}
     */
  var UTF8ToString = (ptr, maxBytesToRead, ignoreNul) => {
      assert(typeof ptr == 'number', `UTF8ToString expects a number (got ${typeof ptr})`);
      return ptr ? UTF8ArrayToString(HEAPU8, ptr, maxBytesToRead, ignoreNul) : '';
    };
  
  var strError = (errno) => UTF8ToString(_strerror(errno));
  
  var ERRNO_CODES = {
      'EPERM': 63,
      'ENOENT': 44,
      'ESRCH': 71,
      'EINTR': 27,
      'EIO': 29,
      'ENXIO': 60,
      'E2BIG': 1,
      'ENOEXEC': 45,
      'EBADF': 8,
      'ECHILD': 12,
      'EAGAIN': 6,
      'EWOULDBLOCK': 6,
      'ENOMEM': 48,
      'EACCES': 2,
      'EFAULT': 21,
      'ENOTBLK': 105,
      'EBUSY': 10,
      'EEXIST': 20,
      'EXDEV': 75,
      'ENODEV': 43,
      'ENOTDIR': 54,
      'EISDIR': 31,
      'EINVAL': 28,
      'ENFILE': 41,
      'EMFILE': 33,
      'ENOTTY': 59,
      'ETXTBSY': 74,
      'EFBIG': 22,
      'ENOSPC': 51,
      'ESPIPE': 70,
      'EROFS': 69,
      'EMLINK': 34,
      'EPIPE': 64,
      'EDOM': 18,
      'ERANGE': 68,
      'ENOMSG': 49,
      'EIDRM': 24,
      'ECHRNG': 106,
      'EL2NSYNC': 156,
      'EL3HLT': 107,
      'EL3RST': 108,
      'ELNRNG': 109,
      'EUNATCH': 110,
      'ENOCSI': 111,
      'EL2HLT': 112,
      'EDEADLK': 16,
      'ENOLCK': 46,
      'EBADE': 113,
      'EBADR': 114,
      'EXFULL': 115,
      'ENOANO': 104,
      'EBADRQC': 103,
      'EBADSLT': 102,
      'EDEADLOCK': 16,
      'EBFONT': 101,
      'ENOSTR': 100,
      'ENODATA': 116,
      'ETIME': 117,
      'ENOSR': 118,
      'ENONET': 119,
      'ENOPKG': 120,
      'EREMOTE': 121,
      'ENOLINK': 47,
      'EADV': 122,
      'ESRMNT': 123,
      'ECOMM': 124,
      'EPROTO': 65,
      'EMULTIHOP': 36,
      'EDOTDOT': 125,
      'EBADMSG': 9,
      'ENOTUNIQ': 126,
      'EBADFD': 127,
      'EREMCHG': 128,
      'ELIBACC': 129,
      'ELIBBAD': 130,
      'ELIBSCN': 131,
      'ELIBMAX': 132,
      'ELIBEXEC': 133,
      'ENOSYS': 52,
      'ENOTEMPTY': 55,
      'ENAMETOOLONG': 37,
      'ELOOP': 32,
      'EOPNOTSUPP': 138,
      'EPFNOSUPPORT': 139,
      'ECONNRESET': 15,
      'ENOBUFS': 42,
      'EAFNOSUPPORT': 5,
      'EPROTOTYPE': 67,
      'ENOTSOCK': 57,
      'ENOPROTOOPT': 50,
      'ESHUTDOWN': 140,
      'ECONNREFUSED': 14,
      'EADDRINUSE': 3,
      'ECONNABORTED': 13,
      'ENETUNREACH': 40,
      'ENETDOWN': 38,
      'ETIMEDOUT': 73,
      'EHOSTDOWN': 142,
      'EHOSTUNREACH': 23,
      'EINPROGRESS': 26,
      'EALREADY': 7,
      'EDESTADDRREQ': 17,
      'EMSGSIZE': 35,
      'EPROTONOSUPPORT': 66,
      'ESOCKTNOSUPPORT': 137,
      'EADDRNOTAVAIL': 4,
      'ENETRESET': 39,
      'EISCONN': 30,
      'ENOTCONN': 53,
      'ETOOMANYREFS': 141,
      'EUSERS': 136,
      'EDQUOT': 19,
      'ESTALE': 72,
      'ENOTSUP': 138,
      'ENOMEDIUM': 148,
      'EILSEQ': 25,
      'EOVERFLOW': 61,
      'ECANCELED': 11,
      'ENOTRECOVERABLE': 56,
      'EOWNERDEAD': 62,
      'ESTRPIPE': 135,
    };
  
  var asyncLoad = async (url) => {
      var arrayBuffer = await readAsync(url);
      assert(arrayBuffer, `Loading data file "${url}" failed (no arrayBuffer).`);
      return new Uint8Array(arrayBuffer);
    };
  
  
  var FS_createDataFile = (...args) => FS.createDataFile(...args);
  
  var getUniqueRunDependency = (id) => {
      var orig = id;
      while (1) {
        if (!runDependencyTracking[id]) return id;
        id = orig + Math.random();
      }
    };
  
  var runDependencies = 0;
  
  
  var dependenciesFulfilled = null;
  
  var runDependencyTracking = {
  };
  
  var runDependencyWatcher = null;
  var removeRunDependency = (id) => {
      runDependencies--;
  
      Module['monitorRunDependencies']?.(runDependencies);
  
      assert(id, 'removeRunDependency requires an ID');
      assert(runDependencyTracking[id]);
      delete runDependencyTracking[id];
      if (runDependencies == 0) {
        if (runDependencyWatcher !== null) {
          clearInterval(runDependencyWatcher);
          runDependencyWatcher = null;
        }
        if (dependenciesFulfilled) {
          var callback = dependenciesFulfilled;
          dependenciesFulfilled = null;
          callback(); // can add another dependenciesFulfilled
        }
      }
    };
  
  
  var addRunDependency = (id) => {
      runDependencies++;
  
      Module['monitorRunDependencies']?.(runDependencies);
  
      assert(id, 'addRunDependency requires an ID')
      assert(!runDependencyTracking[id]);
      runDependencyTracking[id] = 1;
      if (runDependencyWatcher === null && globalThis.setInterval) {
        // Check for missing dependencies every few seconds
        runDependencyWatcher = setInterval(() => {
          if (ABORT) {
            clearInterval(runDependencyWatcher);
            runDependencyWatcher = null;
            return;
          }
          var shown = false;
          for (var dep in runDependencyTracking) {
            if (!shown) {
              shown = true;
              err('still waiting on run dependencies:');
            }
            err(`dependency: ${dep}`);
          }
          if (shown) {
            err('(end of list)');
          }
        }, 10000);
        // Prevent this timer from keeping the runtime alive if nothing
        // else is.
        runDependencyWatcher.unref?.()
      }
    };
  
  
  var preloadPlugins = [];
  var FS_handledByPreloadPlugin = async (byteArray, fullname) => {
      // Ensure plugins are ready.
      if (typeof Browser != 'undefined') Browser.init();
  
      for (var plugin of preloadPlugins) {
        if (plugin['canHandle'](fullname)) {
          assert(plugin['handle'].constructor.name === 'AsyncFunction', 'Filesystem plugin handlers must be async functions (See #24914)')
          return plugin['handle'](byteArray, fullname);
        }
      }
      // In no plugin handled this file then return the original/unmodified
      // byteArray.
      return byteArray;
    };
  var FS_preloadFile = async (parent, name, url, canRead, canWrite, dontCreateFile, canOwn, preFinish) => {
      // TODO we should allow people to just pass in a complete filename instead
      // of parent and name being that we just join them anyways
      var fullname = name ? PATH_FS.resolve(PATH.join2(parent, name)) : parent;
      var dep = getUniqueRunDependency(`cp ${fullname}`); // might have several active requests for the same fullname
      addRunDependency(dep);
  
      try {
        var byteArray = url;
        if (typeof url == 'string') {
          byteArray = await asyncLoad(url);
        }
  
        byteArray = await FS_handledByPreloadPlugin(byteArray, fullname);
        preFinish?.();
        if (!dontCreateFile) {
          FS_createDataFile(parent, name, byteArray, canRead, canWrite, canOwn);
        }
      } finally {
        removeRunDependency(dep);
      }
    };
  var FS_createPreloadedFile = (parent, name, url, canRead, canWrite, onload, onerror, dontCreateFile, canOwn, preFinish) => {
      FS_preloadFile(parent, name, url, canRead, canWrite, dontCreateFile, canOwn, preFinish).then(onload).catch(onerror);
    };
  var FS = {
  root:null,
  mounts:[],
  devices:{
  },
  streams:[],
  nextInode:1,
  nameTable:null,
  currentPath:"/",
  initialized:false,
  ignorePermissions:true,
  filesystems:null,
  syncFSRequests:0,
  readFiles:{
  },
  ErrnoError:class extends Error {
        name = 'ErrnoError';
        // We set the `name` property to be able to identify `FS.ErrnoError`
        // - the `name` is a standard ECMA-262 property of error objects. Kind of good to have it anyway.
        // - when using PROXYFS, an error can come from an underlying FS
        // as different FS objects have their own FS.ErrnoError each,
        // the test `err instanceof FS.ErrnoError` won't detect an error coming from another filesystem, causing bugs.
        // we'll use the reliable test `err.name == "ErrnoError"` instead
        constructor(errno) {
          super(runtimeInitialized ? strError(errno) : '');
          this.errno = errno;
          for (var key in ERRNO_CODES) {
            if (ERRNO_CODES[key] === errno) {
              this.code = key;
              break;
            }
          }
        }
      },
  FSStream:class {
        shared = {};
        get object() {
          return this.node;
        }
        set object(val) {
          this.node = val;
        }
        get isRead() {
          return (this.flags & 2097155) !== 1;
        }
        get isWrite() {
          return (this.flags & 2097155) !== 0;
        }
        get isAppend() {
          return (this.flags & 1024);
        }
        get flags() {
          return this.shared.flags;
        }
        set flags(val) {
          this.shared.flags = val;
        }
        get position() {
          return this.shared.position;
        }
        set position(val) {
          this.shared.position = val;
        }
      },
  FSNode:class {
        node_ops = {};
        stream_ops = {};
        readMode = 292 | 73;
        writeMode = 146;
        mounted = null;
        constructor(parent, name, mode, rdev) {
          if (!parent) {
            parent = this;  // root node sets parent to itself
          }
          this.parent = parent;
          this.mount = parent.mount;
          this.id = FS.nextInode++;
          this.name = name;
          this.mode = mode;
          this.rdev = rdev;
          this.atime = this.mtime = this.ctime = Date.now();
        }
        get read() {
          return (this.mode & this.readMode) === this.readMode;
        }
        set read(val) {
          val ? this.mode |= this.readMode : this.mode &= ~this.readMode;
        }
        get write() {
          return (this.mode & this.writeMode) === this.writeMode;
        }
        set write(val) {
          val ? this.mode |= this.writeMode : this.mode &= ~this.writeMode;
        }
        get isFolder() {
          return FS.isDir(this.mode);
        }
        get isDevice() {
          return FS.isChrdev(this.mode);
        }
      },
  lookupPath(path, opts = {}) {
        if (!path) {
          throw new FS.ErrnoError(44);
        }
        opts.follow_mount ??= true
  
        if (!PATH.isAbs(path)) {
          path = FS.cwd() + '/' + path;
        }
  
        // limit max consecutive symlinks to 40 (SYMLOOP_MAX).
        linkloop: for (var nlinks = 0; nlinks < 40; nlinks++) {
          // split the absolute path
          var parts = path.split('/').filter((p) => !!p);
  
          // start at the root
          var current = FS.root;
          var current_path = '/';
  
          for (var i = 0; i < parts.length; i++) {
            var islast = (i === parts.length-1);
            if (islast && opts.parent) {
              // stop resolving
              break;
            }
  
            if (parts[i] === '.') {
              continue;
            }
  
            if (parts[i] === '..') {
              current_path = PATH.dirname(current_path);
              if (FS.isRoot(current)) {
                path = current_path + '/' + parts.slice(i + 1).join('/');
                // We're making progress here, don't let many consecutive ..'s
                // lead to ELOOP
                nlinks--;
                continue linkloop;
              } else {
                current = current.parent;
              }
              continue;
            }
  
            current_path = PATH.join2(current_path, parts[i]);
            try {
              current = FS.lookupNode(current, parts[i]);
            } catch (e) {
              // if noent_okay is true, suppress a ENOENT in the last component
              // and return an object with an undefined node. This is needed for
              // resolving symlinks in the path when creating a file.
              if ((e?.errno === 44) && islast && opts.noent_okay) {
                return { path: current_path };
              }
              throw e;
            }
  
            // jump to the mount's root node if this is a mountpoint
            if (FS.isMountpoint(current) && (!islast || opts.follow_mount)) {
              current = current.mounted.root;
            }
  
            // by default, lookupPath will not follow a symlink if it is the final path component.
            // setting opts.follow = true will override this behavior.
            if (FS.isLink(current.mode) && (!islast || opts.follow)) {
              if (!current.node_ops.readlink) {
                throw new FS.ErrnoError(52);
              }
              var link = current.node_ops.readlink(current);
              if (!PATH.isAbs(link)) {
                link = PATH.dirname(current_path) + '/' + link;
              }
              path = link + '/' + parts.slice(i + 1).join('/');
              continue linkloop;
            }
          }
          return { path: current_path, node: current };
        }
        throw new FS.ErrnoError(32);
      },
  getPath(node) {
        var path;
        while (true) {
          if (FS.isRoot(node)) {
            var mount = node.mount.mountpoint;
            if (!path) return mount;
            return mount[mount.length-1] !== '/' ? `${mount}/${path}` : mount + path;
          }
          path = path ? `${node.name}/${path}` : node.name;
          node = node.parent;
        }
      },
  hashName(parentid, name) {
        var hash = 0;
  
        for (var i = 0; i < name.length; i++) {
          hash = ((hash << 5) - hash + name.charCodeAt(i)) | 0;
        }
        return ((parentid + hash) >>> 0) % FS.nameTable.length;
      },
  hashAddNode(node) {
        var hash = FS.hashName(node.parent.id, node.name);
        node.name_next = FS.nameTable[hash];
        FS.nameTable[hash] = node;
      },
  hashRemoveNode(node) {
        var hash = FS.hashName(node.parent.id, node.name);
        if (FS.nameTable[hash] === node) {
          FS.nameTable[hash] = node.name_next;
        } else {
          var current = FS.nameTable[hash];
          while (current) {
            if (current.name_next === node) {
              current.name_next = node.name_next;
              break;
            }
            current = current.name_next;
          }
        }
      },
  lookupNode(parent, name) {
        var errCode = FS.mayLookup(parent);
        if (errCode) {
          throw new FS.ErrnoError(errCode);
        }
        var hash = FS.hashName(parent.id, name);
        for (var node = FS.nameTable[hash]; node; node = node.name_next) {
          var nodeName = node.name;
          if (node.parent.id === parent.id && nodeName === name) {
            return node;
          }
        }
        // if we failed to find it in the cache, call into the VFS
        return FS.lookup(parent, name);
      },
  createNode(parent, name, mode, rdev) {
        assert(typeof parent == 'object')
        var node = new FS.FSNode(parent, name, mode, rdev);
  
        FS.hashAddNode(node);
  
        return node;
      },
  destroyNode(node) {
        FS.hashRemoveNode(node);
      },
  isRoot(node) {
        return node === node.parent;
      },
  isMountpoint(node) {
        return !!node.mounted;
      },
  isFile(mode) {
        return (mode & 61440) === 32768;
      },
  isDir(mode) {
        return (mode & 61440) === 16384;
      },
  isLink(mode) {
        return (mode & 61440) === 40960;
      },
  isChrdev(mode) {
        return (mode & 61440) === 8192;
      },
  isBlkdev(mode) {
        return (mode & 61440) === 24576;
      },
  isFIFO(mode) {
        return (mode & 61440) === 4096;
      },
  isSocket(mode) {
        return (mode & 49152) === 49152;
      },
  flagsToPermissionString(flag) {
        var perms = ['r', 'w', 'rw'][flag & 3];
        if ((flag & 512)) {
          perms += 'w';
        }
        return perms;
      },
  nodePermissions(node, perms) {
        if (FS.ignorePermissions) {
          return 0;
        }
        // return 0 if any user, group or owner bits are set.
        if (perms.includes('r') && !(node.mode & 292)) {
          return 2;
        } else if (perms.includes('w') && !(node.mode & 146)) {
          return 2;
        } else if (perms.includes('x') && !(node.mode & 73)) {
          return 2;
        }
        return 0;
      },
  mayLookup(dir) {
        if (!FS.isDir(dir.mode)) return 54;
        var errCode = FS.nodePermissions(dir, 'x');
        if (errCode) return errCode;
        if (!dir.node_ops.lookup) return 2;
        return 0;
      },
  mayCreate(dir, name) {
        if (!FS.isDir(dir.mode)) {
          return 54;
        }
        try {
          var node = FS.lookupNode(dir, name);
          return 20;
        } catch (e) {
        }
        return FS.nodePermissions(dir, 'wx');
      },
  mayDelete(dir, name, isdir) {
        var node;
        try {
          node = FS.lookupNode(dir, name);
        } catch (e) {
          return e.errno;
        }
        var errCode = FS.nodePermissions(dir, 'wx');
        if (errCode) {
          return errCode;
        }
        if (isdir) {
          if (!FS.isDir(node.mode)) {
            return 54;
          }
          if (FS.isRoot(node) || FS.getPath(node) === FS.cwd()) {
            return 10;
          }
        } else {
          if (FS.isDir(node.mode)) {
            return 31;
          }
        }
        return 0;
      },
  mayOpen(node, flags) {
        if (!node) {
          return 44;
        }
        if (FS.isLink(node.mode)) {
          return 32;
        } else if (FS.isDir(node.mode)) {
          if (FS.flagsToPermissionString(flags) !== 'r' // opening for write
              || (flags & (512 | 64))) { // TODO: check for O_SEARCH? (== search for dir only)
            return 31;
          }
        }
        return FS.nodePermissions(node, FS.flagsToPermissionString(flags));
      },
  checkOpExists(op, err) {
        if (!op) {
          throw new FS.ErrnoError(err);
        }
        return op;
      },
  MAX_OPEN_FDS:4096,
  nextfd() {
        for (var fd = 0; fd <= FS.MAX_OPEN_FDS; fd++) {
          if (!FS.streams[fd]) {
            return fd;
          }
        }
        throw new FS.ErrnoError(33);
      },
  getStreamChecked(fd) {
        var stream = FS.getStream(fd);
        if (!stream) {
          throw new FS.ErrnoError(8);
        }
        return stream;
      },
  getStream:(fd) => FS.streams[fd],
  createStream(stream, fd = -1) {
        assert(fd >= -1);
  
        // clone it, so we can return an instance of FSStream
        stream = Object.assign(new FS.FSStream(), stream);
        if (fd == -1) {
          fd = FS.nextfd();
        }
        stream.fd = fd;
        FS.streams[fd] = stream;
        return stream;
      },
  closeStream(fd) {
        FS.streams[fd] = null;
      },
  dupStream(origStream, fd = -1) {
        var stream = FS.createStream(origStream, fd);
        stream.stream_ops?.dup?.(stream);
        return stream;
      },
  doSetAttr(stream, node, attr) {
        var setattr = stream?.stream_ops.setattr;
        var arg = setattr ? stream : node;
        setattr ??= node.node_ops.setattr;
        FS.checkOpExists(setattr, 63)
        setattr(arg, attr);
      },
  chrdev_stream_ops:{
  open(stream) {
          var device = FS.getDevice(stream.node.rdev);
          // override node's stream ops with the device's
          stream.stream_ops = device.stream_ops;
          // forward the open call
          stream.stream_ops.open?.(stream);
        },
  llseek() {
          throw new FS.ErrnoError(70);
        },
  },
  major:(dev) => ((dev) >> 8),
  minor:(dev) => ((dev) & 0xff),
  makedev:(ma, mi) => ((ma) << 8 | (mi)),
  registerDevice(dev, ops) {
        FS.devices[dev] = { stream_ops: ops };
      },
  getDevice:(dev) => FS.devices[dev],
  getMounts(mount) {
        var mounts = [];
        var check = [mount];
  
        while (check.length) {
          var m = check.pop();
  
          mounts.push(m);
  
          check.push(...m.mounts);
        }
  
        return mounts;
      },
  syncfs(populate, callback) {
        if (typeof populate == 'function') {
          callback = populate;
          populate = false;
        }
  
        FS.syncFSRequests++;
  
        if (FS.syncFSRequests > 1) {
          err(`warning: ${FS.syncFSRequests} FS.syncfs operations in flight at once, probably just doing extra work`);
        }
  
        var mounts = FS.getMounts(FS.root.mount);
        var completed = 0;
  
        function doCallback(errCode) {
          assert(FS.syncFSRequests > 0);
          FS.syncFSRequests--;
          return callback(errCode);
        }
  
        function done(errCode) {
          if (errCode) {
            if (!done.errored) {
              done.errored = true;
              return doCallback(errCode);
            }
            return;
          }
          if (++completed >= mounts.length) {
            doCallback(null);
          }
        };
  
        // sync all mounts
        for (var mount of mounts) {
          if (mount.type.syncfs) {
            mount.type.syncfs(mount, populate, done);
          } else {
            done(null);
          }
        }
      },
  mount(type, opts, mountpoint) {
        if (typeof type == 'string') {
          // The filesystem was not included, and instead we have an error
          // message stored in the variable.
          throw type;
        }
        var root = mountpoint === '/';
        var pseudo = !mountpoint;
        var node;
  
        if (root && FS.root) {
          throw new FS.ErrnoError(10);
        } else if (!root && !pseudo) {
          var lookup = FS.lookupPath(mountpoint, { follow_mount: false });
  
          mountpoint = lookup.path;  // use the absolute path
          node = lookup.node;
  
          if (FS.isMountpoint(node)) {
            throw new FS.ErrnoError(10);
          }
  
          if (!FS.isDir(node.mode)) {
            throw new FS.ErrnoError(54);
          }
        }
  
        var mount = {
          type,
          opts,
          mountpoint,
          mounts: []
        };
  
        // create a root node for the fs
        var mountRoot = type.mount(mount);
        mountRoot.mount = mount;
        mount.root = mountRoot;
  
        if (root) {
          FS.root = mountRoot;
        } else if (node) {
          // set as a mountpoint
          node.mounted = mount;
  
          // add the new mount to the current mount's children
          if (node.mount) {
            node.mount.mounts.push(mount);
          }
        }
  
        return mountRoot;
      },
  unmount(mountpoint) {
        var lookup = FS.lookupPath(mountpoint, { follow_mount: false });
  
        if (!FS.isMountpoint(lookup.node)) {
          throw new FS.ErrnoError(28);
        }
  
        // destroy the nodes for this mount, and all its child mounts
        var node = lookup.node;
        var mount = node.mounted;
        var mounts = FS.getMounts(mount);
  
        for (var [hash, current] of Object.entries(FS.nameTable)) {
          while (current) {
            var next = current.name_next;
  
            if (mounts.includes(current.mount)) {
              FS.destroyNode(current);
            }
  
            current = next;
          }
        }
  
        // no longer a mountpoint
        node.mounted = null;
  
        // remove this mount from the child mounts
        var idx = node.mount.mounts.indexOf(mount);
        assert(idx !== -1);
        node.mount.mounts.splice(idx, 1);
      },
  lookup(parent, name) {
        return parent.node_ops.lookup(parent, name);
      },
  mknod(path, mode, dev) {
        var lookup = FS.lookupPath(path, { parent: true });
        var parent = lookup.node;
        var name = PATH.basename(path);
        if (!name) {
          throw new FS.ErrnoError(28);
        }
        if (name === '.' || name === '..') {
          throw new FS.ErrnoError(20);
        }
        var errCode = FS.mayCreate(parent, name);
        if (errCode) {
          throw new FS.ErrnoError(errCode);
        }
        if (!parent.node_ops.mknod) {
          throw new FS.ErrnoError(63);
        }
        return parent.node_ops.mknod(parent, name, mode, dev);
      },
  statfs(path) {
        return FS.statfsNode(FS.lookupPath(path, {follow: true}).node);
      },
  statfsStream(stream) {
        // We keep a separate statfsStream function because noderawfs overrides
        // it. In noderawfs, stream.node is sometimes null. Instead, we need to
        // look at stream.path.
        return FS.statfsNode(stream.node);
      },
  statfsNode(node) {
        // NOTE: None of the defaults here are true. We're just returning safe and
        //       sane values. Currently nodefs and rawfs replace these defaults,
        //       other file systems leave them alone.
        var rtn = {
          bsize: 4096,
          frsize: 4096,
          blocks: 1e6,
          bfree: 5e5,
          bavail: 5e5,
          files: FS.nextInode,
          ffree: FS.nextInode - 1,
          fsid: 42,
          flags: 2,
          namelen: 255,
        };
  
        if (node.node_ops.statfs) {
          Object.assign(rtn, node.node_ops.statfs(node.mount.opts.root));
        }
        return rtn;
      },
  create(path, mode = 0o666) {
        mode &= 4095;
        mode |= 32768;
        return FS.mknod(path, mode, 0);
      },
  mkdir(path, mode = 0o777) {
        mode &= 511 | 512;
        mode |= 16384;
        return FS.mknod(path, mode, 0);
      },
  mkdirTree(path, mode) {
        var dirs = path.split('/');
        var d = '';
        for (var dir of dirs) {
          if (!dir) continue;
          if (d || PATH.isAbs(path)) d += '/';
          d += dir;
          try {
            FS.mkdir(d, mode);
          } catch(e) {
            if (e.errno != 20) throw e;
          }
        }
      },
  mkdev(path, mode, dev) {
        if (typeof dev == 'undefined') {
          dev = mode;
          mode = 0o666;
        }
        mode |= 8192;
        return FS.mknod(path, mode, dev);
      },
  symlink(oldpath, newpath) {
        if (!PATH_FS.resolve(oldpath)) {
          throw new FS.ErrnoError(44);
        }
        var lookup = FS.lookupPath(newpath, { parent: true });
        var parent = lookup.node;
        if (!parent) {
          throw new FS.ErrnoError(44);
        }
        var newname = PATH.basename(newpath);
        var errCode = FS.mayCreate(parent, newname);
        if (errCode) {
          throw new FS.ErrnoError(errCode);
        }
        if (!parent.node_ops.symlink) {
          throw new FS.ErrnoError(63);
        }
        return parent.node_ops.symlink(parent, newname, oldpath);
      },
  rename(old_path, new_path) {
        var old_dirname = PATH.dirname(old_path);
        var new_dirname = PATH.dirname(new_path);
        var old_name = PATH.basename(old_path);
        var new_name = PATH.basename(new_path);
        // parents must exist
        var lookup, old_dir, new_dir;
  
        // let the errors from non existent directories percolate up
        lookup = FS.lookupPath(old_path, { parent: true });
        old_dir = lookup.node;
        lookup = FS.lookupPath(new_path, { parent: true });
        new_dir = lookup.node;
  
        if (!old_dir || !new_dir) throw new FS.ErrnoError(44);
        // need to be part of the same mount
        if (old_dir.mount !== new_dir.mount) {
          throw new FS.ErrnoError(75);
        }
        // source must exist
        var old_node = FS.lookupNode(old_dir, old_name);
        // old path should not be an ancestor of the new path
        var relative = PATH_FS.relative(old_path, new_dirname);
        if (relative.charAt(0) !== '.') {
          throw new FS.ErrnoError(28);
        }
        // new path should not be an ancestor of the old path
        relative = PATH_FS.relative(new_path, old_dirname);
        if (relative.charAt(0) !== '.') {
          throw new FS.ErrnoError(55);
        }
        // see if the new path already exists
        var new_node;
        try {
          new_node = FS.lookupNode(new_dir, new_name);
        } catch (e) {
          // not fatal
        }
        // early out if nothing needs to change
        if (old_node === new_node) {
          return;
        }
        // we'll need to delete the old entry
        var isdir = FS.isDir(old_node.mode);
        var errCode = FS.mayDelete(old_dir, old_name, isdir);
        if (errCode) {
          throw new FS.ErrnoError(errCode);
        }
        // need delete permissions if we'll be overwriting.
        // need create permissions if new doesn't already exist.
        errCode = new_node ?
          FS.mayDelete(new_dir, new_name, isdir) :
          FS.mayCreate(new_dir, new_name);
        if (errCode) {
          throw new FS.ErrnoError(errCode);
        }
        if (!old_dir.node_ops.rename) {
          throw new FS.ErrnoError(63);
        }
        if (FS.isMountpoint(old_node) || (new_node && FS.isMountpoint(new_node))) {
          throw new FS.ErrnoError(10);
        }
        // if we are going to change the parent, check write permissions
        if (new_dir !== old_dir) {
          errCode = FS.nodePermissions(old_dir, 'w');
          if (errCode) {
            throw new FS.ErrnoError(errCode);
          }
        }
        // remove the node from the lookup hash
        FS.hashRemoveNode(old_node);
        // do the underlying fs rename
        try {
          old_dir.node_ops.rename(old_node, new_dir, new_name);
          // update old node (we do this here to avoid each backend
          // needing to)
          old_node.parent = new_dir;
        } catch (e) {
          throw e;
        } finally {
          // add the node back to the hash (in case node_ops.rename
          // changed its name)
          FS.hashAddNode(old_node);
        }
      },
  rmdir(path) {
        var lookup = FS.lookupPath(path, { parent: true });
        var parent = lookup.node;
        var name = PATH.basename(path);
        var node = FS.lookupNode(parent, name);
        var errCode = FS.mayDelete(parent, name, true);
        if (errCode) {
          throw new FS.ErrnoError(errCode);
        }
        if (!parent.node_ops.rmdir) {
          throw new FS.ErrnoError(63);
        }
        if (FS.isMountpoint(node)) {
          throw new FS.ErrnoError(10);
        }
        parent.node_ops.rmdir(parent, name);
        FS.destroyNode(node);
      },
  readdir(path) {
        var lookup = FS.lookupPath(path, { follow: true });
        var node = lookup.node;
        var readdir = FS.checkOpExists(node.node_ops.readdir, 54);
        return readdir(node);
      },
  unlink(path) {
        var lookup = FS.lookupPath(path, { parent: true });
        var parent = lookup.node;
        if (!parent) {
          throw new FS.ErrnoError(44);
        }
        var name = PATH.basename(path);
        var node = FS.lookupNode(parent, name);
        var errCode = FS.mayDelete(parent, name, false);
        if (errCode) {
          // According to POSIX, we should map EISDIR to EPERM, but
          // we instead do what Linux does (and we must, as we use
          // the musl linux libc).
          throw new FS.ErrnoError(errCode);
        }
        if (!parent.node_ops.unlink) {
          throw new FS.ErrnoError(63);
        }
        if (FS.isMountpoint(node)) {
          throw new FS.ErrnoError(10);
        }
        parent.node_ops.unlink(parent, name);
        FS.destroyNode(node);
      },
  readlink(path) {
        var lookup = FS.lookupPath(path);
        var link = lookup.node;
        if (!link) {
          throw new FS.ErrnoError(44);
        }
        if (!link.node_ops.readlink) {
          throw new FS.ErrnoError(28);
        }
        return link.node_ops.readlink(link);
      },
  stat(path, dontFollow) {
        var lookup = FS.lookupPath(path, { follow: !dontFollow });
        var node = lookup.node;
        var getattr = FS.checkOpExists(node.node_ops.getattr, 63);
        return getattr(node);
      },
  fstat(fd) {
        var stream = FS.getStreamChecked(fd);
        var node = stream.node;
        var getattr = stream.stream_ops.getattr;
        var arg = getattr ? stream : node;
        getattr ??= node.node_ops.getattr;
        FS.checkOpExists(getattr, 63)
        return getattr(arg);
      },
  lstat(path) {
        return FS.stat(path, true);
      },
  doChmod(stream, node, mode, dontFollow) {
        FS.doSetAttr(stream, node, {
          mode: (mode & 4095) | (node.mode & ~4095),
          ctime: Date.now(),
          dontFollow
        });
      },
  chmod(path, mode, dontFollow) {
        var node;
        if (typeof path == 'string') {
          var lookup = FS.lookupPath(path, { follow: !dontFollow });
          node = lookup.node;
        } else {
          node = path;
        }
        FS.doChmod(null, node, mode, dontFollow);
      },
  lchmod(path, mode) {
        FS.chmod(path, mode, true);
      },
  fchmod(fd, mode) {
        var stream = FS.getStreamChecked(fd);
        FS.doChmod(stream, stream.node, mode, false);
      },
  doChown(stream, node, dontFollow) {
        FS.doSetAttr(stream, node, {
          timestamp: Date.now(),
          dontFollow
          // we ignore the uid / gid for now
        });
      },
  chown(path, uid, gid, dontFollow) {
        var node;
        if (typeof path == 'string') {
          var lookup = FS.lookupPath(path, { follow: !dontFollow });
          node = lookup.node;
        } else {
          node = path;
        }
        FS.doChown(null, node, dontFollow);
      },
  lchown(path, uid, gid) {
        FS.chown(path, uid, gid, true);
      },
  fchown(fd, uid, gid) {
        var stream = FS.getStreamChecked(fd);
        FS.doChown(stream, stream.node, false);
      },
  doTruncate(stream, node, len) {
        if (FS.isDir(node.mode)) {
          throw new FS.ErrnoError(31);
        }
        if (!FS.isFile(node.mode)) {
          throw new FS.ErrnoError(28);
        }
        var errCode = FS.nodePermissions(node, 'w');
        if (errCode) {
          throw new FS.ErrnoError(errCode);
        }
        FS.doSetAttr(stream, node, {
          size: len,
          timestamp: Date.now()
        });
      },
  truncate(path, len) {
        if (len < 0) {
          throw new FS.ErrnoError(28);
        }
        var node;
        if (typeof path == 'string') {
          var lookup = FS.lookupPath(path, { follow: true });
          node = lookup.node;
        } else {
          node = path;
        }
        FS.doTruncate(null, node, len);
      },
  ftruncate(fd, len) {
        var stream = FS.getStreamChecked(fd);
        if (len < 0 || (stream.flags & 2097155) === 0) {
          throw new FS.ErrnoError(28);
        }
        FS.doTruncate(stream, stream.node, len);
      },
  utime(path, atime, mtime) {
        var lookup = FS.lookupPath(path, { follow: true });
        var node = lookup.node;
        var setattr = FS.checkOpExists(node.node_ops.setattr, 63);
        setattr(node, {
          atime: atime,
          mtime: mtime
        });
      },
  open(path, flags, mode = 0o666) {
        if (path === "") {
          throw new FS.ErrnoError(44);
        }
        flags = typeof flags == 'string' ? FS_modeStringToFlags(flags) : flags;
        if ((flags & 64)) {
          mode = (mode & 4095) | 32768;
        } else {
          mode = 0;
        }
        var node;
        var isDirPath;
        if (typeof path == 'object') {
          node = path;
        } else {
          isDirPath = path.endsWith("/");
          // noent_okay makes it so that if the final component of the path
          // doesn't exist, lookupPath returns `node: undefined`. `path` will be
          // updated to point to the target of all symlinks.
          var lookup = FS.lookupPath(path, {
            follow: !(flags & 131072),
            noent_okay: true
          });
          node = lookup.node;
          path = lookup.path;
        }
        // perhaps we need to create the node
        var created = false;
        if ((flags & 64)) {
          if (node) {
            // if O_CREAT and O_EXCL are set, error out if the node already exists
            if ((flags & 128)) {
              throw new FS.ErrnoError(20);
            }
          } else if (isDirPath) {
            throw new FS.ErrnoError(31);
          } else {
            // node doesn't exist, try to create it
            // Ignore the permission bits here to ensure we can `open` this new
            // file below. We use chmod below the apply the permissions once the
            // file is open.
            node = FS.mknod(path, mode | 0o777, 0);
            created = true;
          }
        }
        if (!node) {
          throw new FS.ErrnoError(44);
        }
        // can't truncate a device
        if (FS.isChrdev(node.mode)) {
          flags &= ~512;
        }
        // if asked only for a directory, then this must be one
        if ((flags & 65536) && !FS.isDir(node.mode)) {
          throw new FS.ErrnoError(54);
        }
        // check permissions, if this is not a file we just created now (it is ok to
        // create and write to a file with read-only permissions; it is read-only
        // for later use)
        if (!created) {
          var errCode = FS.mayOpen(node, flags);
          if (errCode) {
            throw new FS.ErrnoError(errCode);
          }
        }
        // do truncation if necessary
        if ((flags & 512) && !created) {
          FS.truncate(node, 0);
        }
        // we've already handled these, don't pass down to the underlying vfs
        flags &= ~(128 | 512 | 131072);
  
        // register the stream with the filesystem
        var stream = FS.createStream({
          node,
          path: FS.getPath(node),  // we want the absolute path to the node
          flags,
          seekable: true,
          position: 0,
          stream_ops: node.stream_ops,
          // used by the file family libc calls (fopen, fwrite, ferror, etc.)
          ungotten: [],
          error: false
        });
        // call the new stream's open function
        if (stream.stream_ops.open) {
          stream.stream_ops.open(stream);
        }
        if (created) {
          FS.chmod(node, mode & 0o777);
        }
        if (Module['logReadFiles'] && !(flags & 1)) {
          if (!(path in FS.readFiles)) {
            FS.readFiles[path] = 1;
          }
        }
        return stream;
      },
  close(stream) {
        if (FS.isClosed(stream)) {
          throw new FS.ErrnoError(8);
        }
        if (stream.getdents) stream.getdents = null; // free readdir state
        try {
          if (stream.stream_ops.close) {
            stream.stream_ops.close(stream);
          }
        } catch (e) {
          throw e;
        } finally {
          FS.closeStream(stream.fd);
        }
        stream.fd = null;
      },
  isClosed(stream) {
        return stream.fd === null;
      },
  llseek(stream, offset, whence) {
        if (FS.isClosed(stream)) {
          throw new FS.ErrnoError(8);
        }
        if (!stream.seekable || !stream.stream_ops.llseek) {
          throw new FS.ErrnoError(70);
        }
        if (whence != 0 && whence != 1 && whence != 2) {
          throw new FS.ErrnoError(28);
        }
        stream.position = stream.stream_ops.llseek(stream, offset, whence);
        stream.ungotten = [];
        return stream.position;
      },
  read(stream, buffer, offset, length, position) {
        assert(offset >= 0);
        if (length < 0 || position < 0) {
          throw new FS.ErrnoError(28);
        }
        if (FS.isClosed(stream)) {
          throw new FS.ErrnoError(8);
        }
        if ((stream.flags & 2097155) === 1) {
          throw new FS.ErrnoError(8);
        }
        if (FS.isDir(stream.node.mode)) {
          throw new FS.ErrnoError(31);
        }
        if (!stream.stream_ops.read) {
          throw new FS.ErrnoError(28);
        }
        var seeking = typeof position != 'undefined';
        if (!seeking) {
          position = stream.position;
        } else if (!stream.seekable) {
          throw new FS.ErrnoError(70);
        }
        var bytesRead = stream.stream_ops.read(stream, buffer, offset, length, position);
        if (!seeking) stream.position += bytesRead;
        return bytesRead;
      },
  write(stream, buffer, offset, length, position, canOwn) {
        assert(offset >= 0);
        if (length < 0 || position < 0) {
          throw new FS.ErrnoError(28);
        }
        if (FS.isClosed(stream)) {
          throw new FS.ErrnoError(8);
        }
        if ((stream.flags & 2097155) === 0) {
          throw new FS.ErrnoError(8);
        }
        if (FS.isDir(stream.node.mode)) {
          throw new FS.ErrnoError(31);
        }
        if (!stream.stream_ops.write) {
          throw new FS.ErrnoError(28);
        }
        if (stream.seekable && stream.flags & 1024) {
          // seek to the end before writing in append mode
          FS.llseek(stream, 0, 2);
        }
        var seeking = typeof position != 'undefined';
        if (!seeking) {
          position = stream.position;
        } else if (!stream.seekable) {
          throw new FS.ErrnoError(70);
        }
        var bytesWritten = stream.stream_ops.write(stream, buffer, offset, length, position, canOwn);
        if (!seeking) stream.position += bytesWritten;
        return bytesWritten;
      },
  mmap(stream, length, position, prot, flags) {
        // User requests writing to file (prot & PROT_WRITE != 0).
        // Checking if we have permissions to write to the file unless
        // MAP_PRIVATE flag is set. According to POSIX spec it is possible
        // to write to file opened in read-only mode with MAP_PRIVATE flag,
        // as all modifications will be visible only in the memory of
        // the current process.
        if ((prot & 2) !== 0
            && (flags & 2) === 0
            && (stream.flags & 2097155) !== 2) {
          throw new FS.ErrnoError(2);
        }
        if ((stream.flags & 2097155) === 1) {
          throw new FS.ErrnoError(2);
        }
        if (!stream.stream_ops.mmap) {
          throw new FS.ErrnoError(43);
        }
        if (!length) {
          throw new FS.ErrnoError(28);
        }
        return stream.stream_ops.mmap(stream, length, position, prot, flags);
      },
  msync(stream, buffer, offset, length, mmapFlags) {
        assert(offset >= 0);
        if (!stream.stream_ops.msync) {
          return 0;
        }
        return stream.stream_ops.msync(stream, buffer, offset, length, mmapFlags);
      },
  ioctl(stream, cmd, arg) {
        if (!stream.stream_ops.ioctl) {
          throw new FS.ErrnoError(59);
        }
        return stream.stream_ops.ioctl(stream, cmd, arg);
      },
  readFile(path, opts = {}) {
        opts.flags = opts.flags || 0;
        opts.encoding = opts.encoding || 'binary';
        if (opts.encoding !== 'utf8' && opts.encoding !== 'binary') {
          abort(`Invalid encoding type "${opts.encoding}"`);
        }
        var stream = FS.open(path, opts.flags);
        var stat = FS.stat(path);
        var length = stat.size;
        var buf = new Uint8Array(length);
        FS.read(stream, buf, 0, length, 0);
        if (opts.encoding === 'utf8') {
          buf = UTF8ArrayToString(buf);
        }
        FS.close(stream);
        return buf;
      },
  writeFile(path, data, opts = {}) {
        opts.flags = opts.flags || 577;
        var stream = FS.open(path, opts.flags, opts.mode);
        if (typeof data == 'string') {
          data = new Uint8Array(intArrayFromString(data, true));
        }
        if (ArrayBuffer.isView(data)) {
          FS.write(stream, data, 0, data.byteLength, undefined, opts.canOwn);
        } else {
          abort('Unsupported data type');
        }
        FS.close(stream);
      },
  cwd:() => FS.currentPath,
  chdir(path) {
        var lookup = FS.lookupPath(path, { follow: true });
        if (lookup.node === null) {
          throw new FS.ErrnoError(44);
        }
        if (!FS.isDir(lookup.node.mode)) {
          throw new FS.ErrnoError(54);
        }
        var errCode = FS.nodePermissions(lookup.node, 'x');
        if (errCode) {
          throw new FS.ErrnoError(errCode);
        }
        FS.currentPath = lookup.path;
      },
  createDefaultDirectories() {
        FS.mkdir('/tmp');
        FS.mkdir('/home');
        FS.mkdir('/home/web_user');
      },
  createDefaultDevices() {
        // create /dev
        FS.mkdir('/dev');
        // setup /dev/null
        FS.registerDevice(FS.makedev(1, 3), {
          read: () => 0,
          write: (stream, buffer, offset, length, pos) => length,
          llseek: () => 0,
        });
        FS.mkdev('/dev/null', FS.makedev(1, 3));
        // setup /dev/tty and /dev/tty1
        // stderr needs to print output using err() rather than out()
        // so we register a second tty just for it.
        TTY.register(FS.makedev(5, 0), TTY.default_tty_ops);
        TTY.register(FS.makedev(6, 0), TTY.default_tty1_ops);
        FS.mkdev('/dev/tty', FS.makedev(5, 0));
        FS.mkdev('/dev/tty1', FS.makedev(6, 0));
        // setup /dev/[u]random
        // use a buffer to avoid overhead of individual crypto calls per byte
        var randomBuffer = new Uint8Array(1024), randomLeft = 0;
        var randomByte = () => {
          if (randomLeft === 0) {
            randomFill(randomBuffer);
            randomLeft = randomBuffer.byteLength;
          }
          return randomBuffer[--randomLeft];
        };
        FS.createDevice('/dev', 'random', randomByte);
        FS.createDevice('/dev', 'urandom', randomByte);
        // we're not going to emulate the actual shm device,
        // just create the tmp dirs that reside in it commonly
        FS.mkdir('/dev/shm');
        FS.mkdir('/dev/shm/tmp');
      },
  createSpecialDirectories() {
        // create /proc/self/fd which allows /proc/self/fd/6 => readlink gives the
        // name of the stream for fd 6 (see test_unistd_ttyname)
        FS.mkdir('/proc');
        var proc_self = FS.mkdir('/proc/self');
        FS.mkdir('/proc/self/fd');
        FS.mount({
          mount() {
            var node = FS.createNode(proc_self, 'fd', 16895, 73);
            node.stream_ops = {
              llseek: MEMFS.stream_ops.llseek,
            };
            node.node_ops = {
              lookup(parent, name) {
                var fd = +name;
                var stream = FS.getStreamChecked(fd);
                var ret = {
                  parent: null,
                  mount: { mountpoint: 'fake' },
                  node_ops: { readlink: () => stream.path },
                  id: fd + 1,
                };
                ret.parent = ret; // make it look like a simple root node
                return ret;
              },
              readdir() {
                return Array.from(FS.streams.entries())
                  .filter(([k, v]) => v)
                  .map(([k, v]) => k.toString());
              }
            };
            return node;
          }
        }, {}, '/proc/self/fd');
      },
  createStandardStreams(input, output, error) {
        // TODO deprecate the old functionality of a single
        // input / output callback and that utilizes FS.createDevice
        // and instead require a unique set of stream ops
  
        // by default, we symlink the standard streams to the
        // default tty devices. however, if the standard streams
        // have been overwritten we create a unique device for
        // them instead.
        if (input) {
          FS.createDevice('/dev', 'stdin', input);
        } else {
          FS.symlink('/dev/tty', '/dev/stdin');
        }
        if (output) {
          FS.createDevice('/dev', 'stdout', null, output);
        } else {
          FS.symlink('/dev/tty', '/dev/stdout');
        }
        if (error) {
          FS.createDevice('/dev', 'stderr', null, error);
        } else {
          FS.symlink('/dev/tty1', '/dev/stderr');
        }
  
        // open default streams for the stdin, stdout and stderr devices
        var stdin = FS.open('/dev/stdin', 0);
        var stdout = FS.open('/dev/stdout', 1);
        var stderr = FS.open('/dev/stderr', 1);
        assert(stdin.fd === 0, `invalid handle for stdin (${stdin.fd})`);
        assert(stdout.fd === 1, `invalid handle for stdout (${stdout.fd})`);
        assert(stderr.fd === 2, `invalid handle for stderr (${stderr.fd})`);
      },
  staticInit() {
        FS.nameTable = new Array(4096);
  
        FS.mount(MEMFS, {}, '/');
  
        FS.createDefaultDirectories();
        FS.createDefaultDevices();
        FS.createSpecialDirectories();
  
        FS.filesystems = {
          'MEMFS': MEMFS,
        };
      },
  init(input, output, error) {
        assert(!FS.initialized, 'FS.init was previously called. If you want to initialize later with custom parameters, remove any earlier calls (note that one is automatically added to the generated code)');
        FS.initialized = true;
  
        // Allow Module.stdin etc. to provide defaults, if none explicitly passed to us here
        input ??= Module['stdin'];
        output ??= Module['stdout'];
        error ??= Module['stderr'];
  
        FS.createStandardStreams(input, output, error);
      },
  quit() {
        FS.initialized = false;
        // force-flush all streams, so we get musl std streams printed out
        _fflush(0);
        // close all of our streams
        for (var stream of FS.streams) {
          if (stream) {
            FS.close(stream);
          }
        }
      },
  findObject(path, dontResolveLastLink) {
        var ret = FS.analyzePath(path, dontResolveLastLink);
        if (!ret.exists) {
          return null;
        }
        return ret.object;
      },
  analyzePath(path, dontResolveLastLink) {
        // operate from within the context of the symlink's target
        try {
          var lookup = FS.lookupPath(path, { follow: !dontResolveLastLink });
          path = lookup.path;
        } catch (e) {
        }
        var ret = {
          isRoot: false, exists: false, error: 0, name: null, path: null, object: null,
          parentExists: false, parentPath: null, parentObject: null
        };
        try {
          var lookup = FS.lookupPath(path, { parent: true });
          ret.parentExists = true;
          ret.parentPath = lookup.path;
          ret.parentObject = lookup.node;
          ret.name = PATH.basename(path);
          lookup = FS.lookupPath(path, { follow: !dontResolveLastLink });
          ret.exists = true;
          ret.path = lookup.path;
          ret.object = lookup.node;
          ret.name = lookup.node.name;
          ret.isRoot = lookup.path === '/';
        } catch (e) {
          ret.error = e.errno;
        };
        return ret;
      },
  createPath(parent, path, canRead, canWrite) {
        parent = typeof parent == 'string' ? parent : FS.getPath(parent);
        var parts = path.split('/').reverse();
        while (parts.length) {
          var part = parts.pop();
          if (!part) continue;
          var current = PATH.join2(parent, part);
          try {
            FS.mkdir(current);
          } catch (e) {
            if (e.errno != 20) throw e;
          }
          parent = current;
        }
        return current;
      },
  createFile(parent, name, properties, canRead, canWrite) {
        var path = PATH.join2(typeof parent == 'string' ? parent : FS.getPath(parent), name);
        var mode = FS_getMode(canRead, canWrite);
        return FS.create(path, mode);
      },
  createDataFile(parent, name, data, canRead, canWrite, canOwn) {
        var path = name;
        if (parent) {
          parent = typeof parent == 'string' ? parent : FS.getPath(parent);
          path = name ? PATH.join2(parent, name) : parent;
        }
        var mode = FS_getMode(canRead, canWrite);
        var node = FS.create(path, mode);
        if (data) {
          if (typeof data == 'string') {
            var arr = new Array(data.length);
            for (var i = 0, len = data.length; i < len; ++i) arr[i] = data.charCodeAt(i);
            data = arr;
          }
          // make sure we can write to the file
          FS.chmod(node, mode | 146);
          var stream = FS.open(node, 577);
          FS.write(stream, data, 0, data.length, 0, canOwn);
          FS.close(stream);
          FS.chmod(node, mode);
        }
      },
  createDevice(parent, name, input, output) {
        var path = PATH.join2(typeof parent == 'string' ? parent : FS.getPath(parent), name);
        var mode = FS_getMode(!!input, !!output);
        FS.createDevice.major ??= 64;
        var dev = FS.makedev(FS.createDevice.major++, 0);
        // Create a fake device that a set of stream ops to emulate
        // the old behavior.
        FS.registerDevice(dev, {
          open(stream) {
            stream.seekable = false;
          },
          close(stream) {
            // flush any pending line data
            if (output?.buffer?.length) {
              output(10);
            }
          },
          read(stream, buffer, offset, length, pos /* ignored */) {
            var bytesRead = 0;
            for (var i = 0; i < length; i++) {
              var result;
              try {
                result = input();
              } catch (e) {
                throw new FS.ErrnoError(29);
              }
              if (result === undefined && bytesRead === 0) {
                throw new FS.ErrnoError(6);
              }
              if (result === null || result === undefined) break;
              bytesRead++;
              buffer[offset+i] = result;
            }
            if (bytesRead) {
              stream.node.atime = Date.now();
            }
            return bytesRead;
          },
          write(stream, buffer, offset, length, pos) {
            for (var i = 0; i < length; i++) {
              try {
                output(buffer[offset+i]);
              } catch (e) {
                throw new FS.ErrnoError(29);
              }
            }
            if (length) {
              stream.node.mtime = stream.node.ctime = Date.now();
            }
            return i;
          }
        });
        return FS.mkdev(path, mode, dev);
      },
  forceLoadFile(obj) {
        if (obj.isDevice || obj.isFolder || obj.link || obj.contents) return true;
        if (globalThis.XMLHttpRequest) {
          abort("Lazy loading should have been performed (contents set) in createLazyFile, but it was not. Lazy loading only works in web workers. Use --embed-file or --preload-file in emcc on the main thread.");
        } else { // Command-line.
          try {
            obj.contents = readBinary(obj.url);
          } catch (e) {
            throw new FS.ErrnoError(29);
          }
        }
      },
  createLazyFile(parent, name, url, canRead, canWrite) {
        // Lazy chunked Uint8Array (implements get and length from Uint8Array).
        // Actual getting is abstracted away for eventual reuse.
        class LazyUint8Array {
          lengthKnown = false;
          chunks = []; // Loaded chunks. Index is the chunk number
          get(idx) {
            if (idx > this.length-1 || idx < 0) {
              return undefined;
            }
            var chunkOffset = idx % this.chunkSize;
            var chunkNum = (idx / this.chunkSize)|0;
            return this.getter(chunkNum)[chunkOffset];
          }
          setDataGetter(getter) {
            this.getter = getter;
          }
          cacheLength() {
            // Find length
            var xhr = new XMLHttpRequest();
            xhr.open('HEAD', url, false);
            xhr.send(null);
            if (!(xhr.status >= 200 && xhr.status < 300 || xhr.status === 304)) abort("Couldn't load " + url + ". Status: " + xhr.status);
            var datalength = Number(xhr.getResponseHeader("Content-length"));
            var header;
            var hasByteServing = (header = xhr.getResponseHeader("Accept-Ranges")) && header === "bytes";
            var usesGzip = (header = xhr.getResponseHeader("Content-Encoding")) && header === "gzip";
  
            var chunkSize = 1024*1024; // Chunk size in bytes
  
            if (!hasByteServing) chunkSize = datalength;
  
            // Function to get a range from the remote URL.
            var doXHR = (from, to) => {
              if (from > to) abort("invalid range (" + from + ", " + to + ") or no bytes requested!");
              if (to > datalength-1) abort("only " + datalength + " bytes available! programmer error!");
  
              // TODO: Use mozResponseArrayBuffer, responseStream, etc. if available.
              var xhr = new XMLHttpRequest();
              xhr.open('GET', url, false);
              if (datalength !== chunkSize) xhr.setRequestHeader("Range", "bytes=" + from + "-" + to);
  
              // Some hints to the browser that we want binary data.
              xhr.responseType = 'arraybuffer';
              if (xhr.overrideMimeType) {
                xhr.overrideMimeType('text/plain; charset=x-user-defined');
              }
  
              xhr.send(null);
              if (!(xhr.status >= 200 && xhr.status < 300 || xhr.status === 304)) abort("Couldn't load " + url + ". Status: " + xhr.status);
              if (xhr.response !== undefined) {
                return new Uint8Array(/** @type{Array<number>} */(xhr.response || []));
              }
              return intArrayFromString(xhr.responseText || '', true);
            };
            var lazyArray = this;
            lazyArray.setDataGetter((chunkNum) => {
              var start = chunkNum * chunkSize;
              var end = (chunkNum+1) * chunkSize - 1; // including this byte
              end = Math.min(end, datalength-1); // if datalength-1 is selected, this is the last block
              if (typeof lazyArray.chunks[chunkNum] == 'undefined') {
                lazyArray.chunks[chunkNum] = doXHR(start, end);
              }
              if (typeof lazyArray.chunks[chunkNum] == 'undefined') abort('doXHR failed!');
              return lazyArray.chunks[chunkNum];
            });
  
            if (usesGzip || !datalength) {
              // if the server uses gzip or doesn't supply the length, we have to download the whole file to get the (uncompressed) length
              chunkSize = datalength = 1; // this will force getter(0)/doXHR do download the whole file
              datalength = this.getter(0).length;
              chunkSize = datalength;
              out("LazyFiles on gzip forces download of the whole file when length is accessed");
            }
  
            this._length = datalength;
            this._chunkSize = chunkSize;
            this.lengthKnown = true;
          }
          get length() {
            if (!this.lengthKnown) {
              this.cacheLength();
            }
            return this._length;
          }
          get chunkSize() {
            if (!this.lengthKnown) {
              this.cacheLength();
            }
            return this._chunkSize;
          }
        }
  
        if (globalThis.XMLHttpRequest) {
          if (!ENVIRONMENT_IS_WORKER) abort('Cannot do synchronous binary XHRs outside webworkers in modern browsers. Use --embed-file or --preload-file in emcc');
          var lazyArray = new LazyUint8Array();
          var properties = { isDevice: false, contents: lazyArray };
        } else {
          var properties = { isDevice: false, url: url };
        }
  
        var node = FS.createFile(parent, name, properties, canRead, canWrite);
        // This is a total hack, but I want to get this lazy file code out of the
        // core of MEMFS. If we want to keep this lazy file concept I feel it should
        // be its own thin LAZYFS proxying calls to MEMFS.
        if (properties.contents) {
          node.contents = properties.contents;
        } else if (properties.url) {
          node.contents = null;
          node.url = properties.url;
        }
        // Add a function that defers querying the file size until it is asked the first time.
        Object.defineProperties(node, {
          usedBytes: {
            get: function() { return this.contents.length; }
          }
        });
        // override each stream op with one that tries to force load the lazy file first
        var stream_ops = {};
        for (const [key, fn] of Object.entries(node.stream_ops)) {
          stream_ops[key] = (...args) => {
            FS.forceLoadFile(node);
            return fn(...args);
          };
        }
        function writeChunks(stream, buffer, offset, length, position) {
          var contents = stream.node.contents;
          if (position >= contents.length)
            return 0;
          var size = Math.min(contents.length - position, length);
          assert(size >= 0);
          if (contents.slice) { // normal array
            for (var i = 0; i < size; i++) {
              buffer[offset + i] = contents[position + i];
            }
          } else {
            for (var i = 0; i < size; i++) { // LazyUint8Array from sync binary XHR
              buffer[offset + i] = contents.get(position + i);
            }
          }
          return size;
        }
        // use a custom read function
        stream_ops.read = (stream, buffer, offset, length, position) => {
          FS.forceLoadFile(node);
          return writeChunks(stream, buffer, offset, length, position)
        };
        // use a custom mmap function
        stream_ops.mmap = (stream, length, position, prot, flags) => {
          FS.forceLoadFile(node);
          var ptr = mmapAlloc(length);
          if (!ptr) {
            throw new FS.ErrnoError(48);
          }
          writeChunks(stream, HEAP8, ptr, length, position);
          return { ptr, allocated: true };
        };
        node.stream_ops = stream_ops;
        return node;
      },
  absolutePath() {
        abort('FS.absolutePath has been removed; use PATH_FS.resolve instead');
      },
  createFolder() {
        abort('FS.createFolder has been removed; use FS.mkdir instead');
      },
  createLink() {
        abort('FS.createLink has been removed; use FS.symlink instead');
      },
  joinPath() {
        abort('FS.joinPath has been removed; use PATH.join instead');
      },
  mmapAlloc() {
        abort('FS.mmapAlloc has been replaced by the top level function mmapAlloc');
      },
  standardizePath() {
        abort('FS.standardizePath has been removed; use PATH.normalize instead');
      },
  };
  
  var SYSCALLS = {
  DEFAULT_POLLMASK:5,
  calculateAt(dirfd, path, allowEmpty) {
        if (PATH.isAbs(path)) {
          return path;
        }
        // relative path
        var dir;
        if (dirfd === -100) {
          dir = FS.cwd();
        } else {
          var dirstream = SYSCALLS.getStreamFromFD(dirfd);
          dir = dirstream.path;
        }
        if (path.length == 0) {
          if (!allowEmpty) {
            throw new FS.ErrnoError(44);;
          }
          return dir;
        }
        return dir + '/' + path;
      },
  writeStat(buf, stat) {
        HEAPU32[((buf)>>2)] = stat.dev;
        HEAPU32[(((buf)+(4))>>2)] = stat.mode;
        HEAPU32[(((buf)+(8))>>2)] = stat.nlink;
        HEAPU32[(((buf)+(12))>>2)] = stat.uid;
        HEAPU32[(((buf)+(16))>>2)] = stat.gid;
        HEAPU32[(((buf)+(20))>>2)] = stat.rdev;
        HEAP64[(((buf)+(24))>>3)] = BigInt(stat.size);
        HEAP32[(((buf)+(32))>>2)] = 4096;
        HEAP32[(((buf)+(36))>>2)] = stat.blocks;
        var atime = stat.atime.getTime();
        var mtime = stat.mtime.getTime();
        var ctime = stat.ctime.getTime();
        HEAP64[(((buf)+(40))>>3)] = BigInt(Math.floor(atime / 1000));
        HEAPU32[(((buf)+(48))>>2)] = (atime % 1000) * 1000 * 1000;
        HEAP64[(((buf)+(56))>>3)] = BigInt(Math.floor(mtime / 1000));
        HEAPU32[(((buf)+(64))>>2)] = (mtime % 1000) * 1000 * 1000;
        HEAP64[(((buf)+(72))>>3)] = BigInt(Math.floor(ctime / 1000));
        HEAPU32[(((buf)+(80))>>2)] = (ctime % 1000) * 1000 * 1000;
        HEAP64[(((buf)+(88))>>3)] = BigInt(stat.ino);
        return 0;
      },
  writeStatFs(buf, stats) {
        HEAPU32[(((buf)+(4))>>2)] = stats.bsize;
        HEAPU32[(((buf)+(60))>>2)] = stats.bsize;
        HEAP64[(((buf)+(8))>>3)] = BigInt(stats.blocks);
        HEAP64[(((buf)+(16))>>3)] = BigInt(stats.bfree);
        HEAP64[(((buf)+(24))>>3)] = BigInt(stats.bavail);
        HEAP64[(((buf)+(32))>>3)] = BigInt(stats.files);
        HEAP64[(((buf)+(40))>>3)] = BigInt(stats.ffree);
        HEAPU32[(((buf)+(48))>>2)] = stats.fsid;
        HEAPU32[(((buf)+(64))>>2)] = stats.flags;  // ST_NOSUID
        HEAPU32[(((buf)+(56))>>2)] = stats.namelen;
      },
  doMsync(addr, stream, len, flags, offset) {
        if (!FS.isFile(stream.node.mode)) {
          throw new FS.ErrnoError(43);
        }
        if (flags & 2) {
          // MAP_PRIVATE calls need not to be synced back to underlying fs
          return 0;
        }
        var buffer = HEAPU8.slice(addr, addr + len);
        FS.msync(stream, buffer, offset, len, flags);
      },
  getStreamFromFD(fd) {
        var stream = FS.getStreamChecked(fd);
        return stream;
      },
  varargs:undefined,
  getStr(ptr) {
        var ret = UTF8ToString(ptr);
        return ret;
      },
  };
  function ___syscall_chdir(path) {
  try {
  
      path = SYSCALLS.getStr(path);
      FS.chdir(path);
      return 0;
    } catch (e) {
    if (typeof FS == 'undefined' || !(e.name === 'ErrnoError')) throw e;
    return -e.errno;
  }
  }

  function ___syscall_dup3(fd, newfd, flags) {
  try {
  
      var old = SYSCALLS.getStreamFromFD(fd);
      assert(!flags);
      if (old.fd === newfd) return -28;
      // Check newfd is within range of valid open file descriptors.
      if (newfd < 0 || newfd >= FS.MAX_OPEN_FDS) return -8;
      var existing = FS.getStream(newfd);
      if (existing) FS.close(existing);
      return FS.dupStream(old, newfd).fd;
    } catch (e) {
    if (typeof FS == 'undefined' || !(e.name === 'ErrnoError')) throw e;
    return -e.errno;
  }
  }

  function ___syscall_faccessat(dirfd, path, amode, flags) {
  try {
  
      path = SYSCALLS.getStr(path);
      assert(!flags || flags == 512);
      path = SYSCALLS.calculateAt(dirfd, path);
      if (amode & ~7) {
        // need a valid mode
        return -28;
      }
      var lookup = FS.lookupPath(path, { follow: true });
      var node = lookup.node;
      if (!node) {
        return -44;
      }
      var perms = '';
      if (amode & 4) perms += 'r';
      if (amode & 2) perms += 'w';
      if (amode & 1) perms += 'x';
      if (perms /* otherwise, they've just passed F_OK */ && FS.nodePermissions(node, perms)) {
        return -2;
      }
      return 0;
    } catch (e) {
    if (typeof FS == 'undefined' || !(e.name === 'ErrnoError')) throw e;
    return -e.errno;
  }
  }

  var syscallGetVarargI = () => {
      assert(SYSCALLS.varargs != undefined);
      // the `+` prepended here is necessary to convince the JSCompiler that varargs is indeed a number.
      var ret = HEAP32[((+SYSCALLS.varargs)>>2)];
      SYSCALLS.varargs += 4;
      return ret;
    };
  var syscallGetVarargP = syscallGetVarargI;
  
  
  function ___syscall_fcntl64(fd, cmd, varargs) {
  SYSCALLS.varargs = varargs;
  try {
  
      var stream = SYSCALLS.getStreamFromFD(fd);
      switch (cmd) {
        case 0: {
          var arg = syscallGetVarargI();
          if (arg < 0) {
            return -28;
          }
          while (FS.streams[arg]) {
            arg++;
          }
          var newStream;
          newStream = FS.dupStream(stream, arg);
          return newStream.fd;
        }
        case 1:
        case 2:
          return 0;  // FD_CLOEXEC makes no sense for a single process.
        case 3:
          return stream.flags;
        case 4: {
          var arg = syscallGetVarargI();
          stream.flags |= arg;
          return 0;
        }
        case 12: {
          var arg = syscallGetVarargP();
          var offset = 0;
          // We're always unlocked.
          HEAP16[(((arg)+(offset))>>1)] = 2;
          return 0;
        }
        case 13:
        case 14:
          // Pretend that the locking is successful. These are process-level locks,
          // and Emscripten programs are a single process. If we supported linking a
          // filesystem between programs, we'd need to do more here.
          // See https://github.com/emscripten-core/emscripten/issues/23697
          return 0;
      }
      return -28;
    } catch (e) {
    if (typeof FS == 'undefined' || !(e.name === 'ErrnoError')) throw e;
    return -e.errno;
  }
  }

  function ___syscall_fstat64(fd, buf) {
  try {
  
      return SYSCALLS.writeStat(buf, FS.fstat(fd));
    } catch (e) {
    if (typeof FS == 'undefined' || !(e.name === 'ErrnoError')) throw e;
    return -e.errno;
  }
  }

  
  var stringToUTF8 = (str, outPtr, maxBytesToWrite) => {
      assert(typeof maxBytesToWrite == 'number', 'stringToUTF8(str, outPtr, maxBytesToWrite) is missing the third parameter that specifies the length of the output buffer!');
      return stringToUTF8Array(str, HEAPU8, outPtr, maxBytesToWrite);
    };
  function ___syscall_getcwd(buf, size) {
  try {
  
      if (size === 0) return -28;
      var cwd = FS.cwd();
      var cwdLengthInBytes = lengthBytesUTF8(cwd) + 1;
      if (size < cwdLengthInBytes) return -68;
      stringToUTF8(cwd, buf, size);
      return cwdLengthInBytes;
    } catch (e) {
    if (typeof FS == 'undefined' || !(e.name === 'ErrnoError')) throw e;
    return -e.errno;
  }
  }

  
  function ___syscall_getdents64(fd, dirp, count) {
  try {
  
      var stream = SYSCALLS.getStreamFromFD(fd)
      stream.getdents ||= FS.readdir(stream.path);
  
      var struct_size = 280;
      var pos = 0;
      var off = FS.llseek(stream, 0, 1);
  
      var startIdx = Math.floor(off / struct_size);
      var endIdx = Math.min(stream.getdents.length, startIdx + Math.floor(count/struct_size))
      for (var idx = startIdx; idx < endIdx; idx++) {
        var id;
        var type;
        var name = stream.getdents[idx];
        if (name === '.') {
          id = stream.node.id;
          type = 4; // DT_DIR
        }
        else if (name === '..') {
          var lookup = FS.lookupPath(stream.path, { parent: true });
          id = lookup.node.id;
          type = 4; // DT_DIR
        }
        else {
          var child;
          try {
            child = FS.lookupNode(stream.node, name);
          } catch (e) {
            // If the entry is not a directory, file, or symlink, nodefs
            // lookupNode will raise EINVAL. Skip these and continue.
            if (e?.errno === 28) {
              continue;
            }
            throw e;
          }
          id = child.id;
          type = FS.isChrdev(child.mode) ? 2 :  // DT_CHR, character device.
                 FS.isDir(child.mode) ? 4 :     // DT_DIR, directory.
                 FS.isLink(child.mode) ? 10 :   // DT_LNK, symbolic link.
                 8;                             // DT_REG, regular file.
        }
        assert(id);
        HEAP64[((dirp + pos)>>3)] = BigInt(id);
        HEAP64[(((dirp + pos)+(8))>>3)] = BigInt((idx + 1) * struct_size);
        HEAP16[(((dirp + pos)+(16))>>1)] = 280;
        HEAP8[(dirp + pos)+(18)] = type;
        stringToUTF8(name, dirp + pos + 19, 256);
        pos += struct_size;
      }
      FS.llseek(stream, idx * struct_size, 0);
      return pos;
    } catch (e) {
    if (typeof FS == 'undefined' || !(e.name === 'ErrnoError')) throw e;
    return -e.errno;
  }
  }

  
  function ___syscall_ioctl(fd, op, varargs) {
  SYSCALLS.varargs = varargs;
  try {
  
      var stream = SYSCALLS.getStreamFromFD(fd);
      switch (op) {
        case 21509: {
          if (!stream.tty) return -59;
          return 0;
        }
        case 21505: {
          if (!stream.tty) return -59;
          if (stream.tty.ops.ioctl_tcgets) {
            var termios = stream.tty.ops.ioctl_tcgets(stream);
            var argp = syscallGetVarargP();
            HEAP32[((argp)>>2)] = termios.c_iflag || 0;
            HEAP32[(((argp)+(4))>>2)] = termios.c_oflag || 0;
            HEAP32[(((argp)+(8))>>2)] = termios.c_cflag || 0;
            HEAP32[(((argp)+(12))>>2)] = termios.c_lflag || 0;
            for (var i = 0; i < 32; i++) {
              HEAP8[(argp + i)+(17)] = termios.c_cc[i] || 0;
            }
            return 0;
          }
          return 0;
        }
        case 21510:
        case 21511:
        case 21512: {
          if (!stream.tty) return -59;
          return 0; // no-op, not actually adjusting terminal settings
        }
        case 21506:
        case 21507:
        case 21508: {
          if (!stream.tty) return -59;
          if (stream.tty.ops.ioctl_tcsets) {
            var argp = syscallGetVarargP();
            var c_iflag = HEAP32[((argp)>>2)];
            var c_oflag = HEAP32[(((argp)+(4))>>2)];
            var c_cflag = HEAP32[(((argp)+(8))>>2)];
            var c_lflag = HEAP32[(((argp)+(12))>>2)];
            var c_cc = []
            for (var i = 0; i < 32; i++) {
              c_cc.push(HEAP8[(argp + i)+(17)]);
            }
            return stream.tty.ops.ioctl_tcsets(stream.tty, op, { c_iflag, c_oflag, c_cflag, c_lflag, c_cc });
          }
          return 0; // no-op, not actually adjusting terminal settings
        }
        case 21519: {
          if (!stream.tty) return -59;
          var argp = syscallGetVarargP();
          HEAP32[((argp)>>2)] = 0;
          return 0;
        }
        case 21520: {
          if (!stream.tty) return -59;
          return -28; // not supported
        }
        case 21537:
        case 21531: {
          var argp = syscallGetVarargP();
          return FS.ioctl(stream, op, argp);
        }
        case 21523: {
          // TODO: in theory we should write to the winsize struct that gets
          // passed in, but for now musl doesn't read anything on it
          if (!stream.tty) return -59;
          if (stream.tty.ops.ioctl_tiocgwinsz) {
            var winsize = stream.tty.ops.ioctl_tiocgwinsz(stream.tty);
            var argp = syscallGetVarargP();
            HEAP16[((argp)>>1)] = winsize[0];
            HEAP16[(((argp)+(2))>>1)] = winsize[1];
          }
          return 0;
        }
        case 21524: {
          // TODO: technically, this ioctl call should change the window size.
          // but, since emscripten doesn't have any concept of a terminal window
          // yet, we'll just silently throw it away as we do TIOCGWINSZ
          if (!stream.tty) return -59;
          return 0;
        }
        case 21515: {
          if (!stream.tty) return -59;
          return 0;
        }
        default: return -28; // not supported
      }
    } catch (e) {
    if (typeof FS == 'undefined' || !(e.name === 'ErrnoError')) throw e;
    return -e.errno;
  }
  }

  function ___syscall_lstat64(path, buf) {
  try {
  
      path = SYSCALLS.getStr(path);
      return SYSCALLS.writeStat(buf, FS.lstat(path));
    } catch (e) {
    if (typeof FS == 'undefined' || !(e.name === 'ErrnoError')) throw e;
    return -e.errno;
  }
  }

  function ___syscall_mkdirat(dirfd, path, mode) {
  try {
  
      path = SYSCALLS.getStr(path);
      path = SYSCALLS.calculateAt(dirfd, path);
      FS.mkdir(path, mode, 0);
      return 0;
    } catch (e) {
    if (typeof FS == 'undefined' || !(e.name === 'ErrnoError')) throw e;
    return -e.errno;
  }
  }

  function ___syscall_newfstatat(dirfd, path, buf, flags) {
  try {
  
      path = SYSCALLS.getStr(path);
      var nofollow = flags & 256;
      var allowEmpty = flags & 4096;
      flags = flags & (~6400);
      assert(!flags, `unknown flags in __syscall_newfstatat: ${flags}`);
      path = SYSCALLS.calculateAt(dirfd, path, allowEmpty);
      return SYSCALLS.writeStat(buf, nofollow ? FS.lstat(path) : FS.stat(path));
    } catch (e) {
    if (typeof FS == 'undefined' || !(e.name === 'ErrnoError')) throw e;
    return -e.errno;
  }
  }

  
  function ___syscall_openat(dirfd, path, flags, varargs) {
  SYSCALLS.varargs = varargs;
  try {
  
      path = SYSCALLS.getStr(path);
      path = SYSCALLS.calculateAt(dirfd, path);
      var mode = varargs ? syscallGetVarargI() : 0;
      return FS.open(path, flags, mode).fd;
    } catch (e) {
    if (typeof FS == 'undefined' || !(e.name === 'ErrnoError')) throw e;
    return -e.errno;
  }
  }

  
  
  function ___syscall_readlinkat(dirfd, path, buf, bufsize) {
  try {
  
      path = SYSCALLS.getStr(path);
      path = SYSCALLS.calculateAt(dirfd, path);
      if (bufsize <= 0) return -28;
      var ret = FS.readlink(path);
  
      var len = Math.min(bufsize, lengthBytesUTF8(ret));
      var endChar = HEAP8[buf+len];
      stringToUTF8(ret, buf, bufsize+1);
      // readlink is one of the rare functions that write out a C string, but does never append a null to the output buffer(!)
      // stringToUTF8() always appends a null byte, so restore the character under the null byte after the write.
      HEAP8[buf+len] = endChar;
      return len;
    } catch (e) {
    if (typeof FS == 'undefined' || !(e.name === 'ErrnoError')) throw e;
    return -e.errno;
  }
  }

  function ___syscall_renameat(olddirfd, oldpath, newdirfd, newpath) {
  try {
  
      oldpath = SYSCALLS.getStr(oldpath);
      newpath = SYSCALLS.getStr(newpath);
      oldpath = SYSCALLS.calculateAt(olddirfd, oldpath);
      newpath = SYSCALLS.calculateAt(newdirfd, newpath);
      FS.rename(oldpath, newpath);
      return 0;
    } catch (e) {
    if (typeof FS == 'undefined' || !(e.name === 'ErrnoError')) throw e;
    return -e.errno;
  }
  }

  function ___syscall_rmdir(path) {
  try {
  
      path = SYSCALLS.getStr(path);
      FS.rmdir(path);
      return 0;
    } catch (e) {
    if (typeof FS == 'undefined' || !(e.name === 'ErrnoError')) throw e;
    return -e.errno;
  }
  }

  function ___syscall_stat64(path, buf) {
  try {
  
      path = SYSCALLS.getStr(path);
      return SYSCALLS.writeStat(buf, FS.stat(path));
    } catch (e) {
    if (typeof FS == 'undefined' || !(e.name === 'ErrnoError')) throw e;
    return -e.errno;
  }
  }

  function ___syscall_statfs64(path, size, buf) {
  try {
  
      assert(size === 88);
      SYSCALLS.writeStatFs(buf, FS.statfs(SYSCALLS.getStr(path)));
      return 0;
    } catch (e) {
    if (typeof FS == 'undefined' || !(e.name === 'ErrnoError')) throw e;
    return -e.errno;
  }
  }

  function ___syscall_symlinkat(target, dirfd, linkpath) {
  try {
  
      target = SYSCALLS.getStr(target);
      linkpath = SYSCALLS.getStr(linkpath);
      linkpath = SYSCALLS.calculateAt(dirfd, linkpath);
      FS.symlink(target, linkpath);
      return 0;
    } catch (e) {
    if (typeof FS == 'undefined' || !(e.name === 'ErrnoError')) throw e;
    return -e.errno;
  }
  }

  function ___syscall_unlinkat(dirfd, path, flags) {
  try {
  
      path = SYSCALLS.getStr(path);
      path = SYSCALLS.calculateAt(dirfd, path);
      if (!flags) {
        FS.unlink(path);
      } else if (flags === 512) {
        FS.rmdir(path);
      } else {
        return -28;
      }
      return 0;
    } catch (e) {
    if (typeof FS == 'undefined' || !(e.name === 'ErrnoError')) throw e;
    return -e.errno;
  }
  }

  var __abort_js = () =>
      abort('native code called abort()');

  var runtimeKeepaliveCounter = 0;
  var __emscripten_runtime_keepalive_clear = () => {
      noExitRuntime = false;
      runtimeKeepaliveCounter = 0;
    };

  var __emscripten_throw_longjmp = () => {
      throw Infinity;
    };

  var INT53_MAX = 9007199254740992;
  
  var INT53_MIN = -9007199254740992;
  var bigintToI53Checked = (num) => (num < INT53_MIN || num > INT53_MAX) ? NaN : Number(num);
  function __gmtime_js(time, tmPtr) {
    time = bigintToI53Checked(time);
  
  
      var date = new Date(time * 1000);
      HEAP32[((tmPtr)>>2)] = date.getUTCSeconds();
      HEAP32[(((tmPtr)+(4))>>2)] = date.getUTCMinutes();
      HEAP32[(((tmPtr)+(8))>>2)] = date.getUTCHours();
      HEAP32[(((tmPtr)+(12))>>2)] = date.getUTCDate();
      HEAP32[(((tmPtr)+(16))>>2)] = date.getUTCMonth();
      HEAP32[(((tmPtr)+(20))>>2)] = date.getUTCFullYear()-1900;
      HEAP32[(((tmPtr)+(24))>>2)] = date.getUTCDay();
      var start = Date.UTC(date.getUTCFullYear(), 0, 1, 0, 0, 0, 0);
      var yday = ((date.getTime() - start) / (1000 * 60 * 60 * 24))|0;
      HEAP32[(((tmPtr)+(28))>>2)] = yday;
    ;
  }

  var isLeapYear = (year) => year%4 === 0 && (year%100 !== 0 || year%400 === 0);
  
  var MONTH_DAYS_LEAP_CUMULATIVE = [0,31,60,91,121,152,182,213,244,274,305,335];
  
  var MONTH_DAYS_REGULAR_CUMULATIVE = [0,31,59,90,120,151,181,212,243,273,304,334];
  var ydayFromDate = (date) => {
      var leap = isLeapYear(date.getFullYear());
      var monthDaysCumulative = (leap ? MONTH_DAYS_LEAP_CUMULATIVE : MONTH_DAYS_REGULAR_CUMULATIVE);
      var yday = monthDaysCumulative[date.getMonth()] + date.getDate() - 1; // -1 since it's days since Jan 1
  
      return yday;
    };
  
  function __localtime_js(time, tmPtr) {
    time = bigintToI53Checked(time);
  
  
      var date = new Date(time*1000);
      HEAP32[((tmPtr)>>2)] = date.getSeconds();
      HEAP32[(((tmPtr)+(4))>>2)] = date.getMinutes();
      HEAP32[(((tmPtr)+(8))>>2)] = date.getHours();
      HEAP32[(((tmPtr)+(12))>>2)] = date.getDate();
      HEAP32[(((tmPtr)+(16))>>2)] = date.getMonth();
      HEAP32[(((tmPtr)+(20))>>2)] = date.getFullYear()-1900;
      HEAP32[(((tmPtr)+(24))>>2)] = date.getDay();
  
      var yday = ydayFromDate(date)|0;
      HEAP32[(((tmPtr)+(28))>>2)] = yday;
      HEAP32[(((tmPtr)+(36))>>2)] = -(date.getTimezoneOffset() * 60);
  
      // Attention: DST is in December in South, and some regions don't have DST at all.
      var start = new Date(date.getFullYear(), 0, 1);
      var summerOffset = new Date(date.getFullYear(), 6, 1).getTimezoneOffset();
      var winterOffset = start.getTimezoneOffset();
      var dst = (summerOffset != winterOffset && date.getTimezoneOffset() == Math.min(winterOffset, summerOffset))|0;
      HEAP32[(((tmPtr)+(32))>>2)] = dst;
    ;
  }

  
  
  
  
  
  function __mmap_js(len, prot, flags, fd, offset, allocated, addr) {
    offset = bigintToI53Checked(offset);
  
  
  try {
  
      // musl's mmap doesn't allow values over a certain limit
      // see OFF_MASK in mmap.c.
      assert(!isNaN(offset));
      var stream = SYSCALLS.getStreamFromFD(fd);
      var res = FS.mmap(stream, len, offset, prot, flags);
      var ptr = res.ptr;
      HEAP32[((allocated)>>2)] = res.allocated;
      HEAPU32[((addr)>>2)] = ptr;
      return 0;
    } catch (e) {
    if (typeof FS == 'undefined' || !(e.name === 'ErrnoError')) throw e;
    return -e.errno;
  }
  ;
  }

  
  function __munmap_js(addr, len, prot, flags, fd, offset) {
    offset = bigintToI53Checked(offset);
  
  
  try {
  
      var stream = SYSCALLS.getStreamFromFD(fd);
      if (prot & 2) {
        SYSCALLS.doMsync(addr, stream, len, flags, offset);
      }
    } catch (e) {
    if (typeof FS == 'undefined' || !(e.name === 'ErrnoError')) throw e;
    return -e.errno;
  }
  ;
  }

  var timers = {
  };
  
  var handleException = (e) => {
      // Certain exception types we do not treat as errors since they are used for
      // internal control flow.
      // 1. ExitStatus, which is thrown by exit()
      // 2. "unwind", which is thrown by emscripten_unwind_to_js_event_loop() and others
      //    that wish to return to JS event loop.
      if (e instanceof ExitStatus || e == 'unwind') {
        return EXITSTATUS;
      }
      checkStackCookie();
      if (e instanceof WebAssembly.RuntimeError) {
        if (_emscripten_stack_get_current() <= 0) {
          err('Stack overflow detected.  You can try increasing -sSTACK_SIZE (currently set to 65536)');
        }
      }
      quit_(1, e);
    };
  
  
  var keepRuntimeAlive = () => noExitRuntime || runtimeKeepaliveCounter > 0;
  var _proc_exit = (code) => {
      EXITSTATUS = code;
      if (!keepRuntimeAlive()) {
        Module['onExit']?.(code);
        ABORT = true;
      }
      quit_(code, new ExitStatus(code));
    };
  
  
  /** @param {boolean|number=} implicit */
  var exitJS = (status, implicit) => {
      EXITSTATUS = status;
  
      checkUnflushedContent();
  
      // if exit() was called explicitly, warn the user if the runtime isn't actually being shut down
      if (keepRuntimeAlive() && !implicit) {
        var msg = `program exited (with status: ${status}), but keepRuntimeAlive() is set (counter=${runtimeKeepaliveCounter}) due to an async operation, so halting execution but not exiting the runtime or preventing further async execution (you can use emscripten_force_exit, if you want to force a true shutdown)`;
        readyPromiseReject?.(msg);
        err(msg);
      }
  
      _proc_exit(status);
    };
  var _exit = exitJS;
  
  
  var maybeExit = () => {
      if (!keepRuntimeAlive()) {
        try {
          _exit(EXITSTATUS);
        } catch (e) {
          handleException(e);
        }
      }
    };
  var callUserCallback = (func) => {
      if (ABORT) {
        err('user callback triggered after runtime exited or application aborted.  Ignoring.');
        return;
      }
      try {
        func();
        maybeExit();
      } catch (e) {
        handleException(e);
      }
    };
  
  
  var _emscripten_get_now = () => performance.now();
  var __setitimer_js = (which, timeout_ms) => {
      // First, clear any existing timer.
      if (timers[which]) {
        clearTimeout(timers[which].id);
        delete timers[which];
      }
  
      // A timeout of zero simply cancels the current timeout so we have nothing
      // more to do.
      if (!timeout_ms) return 0;
  
      var id = setTimeout(() => {
        assert(which in timers);
        delete timers[which];
        callUserCallback(() => __emscripten_timeout(which, _emscripten_get_now()));
      }, timeout_ms);
      timers[which] = { id, timeout_ms };
      return 0;
    };

  
  var __tzset_js = (timezone, daylight, std_name, dst_name) => {
      // TODO: Use (malleable) environment variables instead of system settings.
      var currentYear = new Date().getFullYear();
      var winter = new Date(currentYear, 0, 1);
      var summer = new Date(currentYear, 6, 1);
      var winterOffset = winter.getTimezoneOffset();
      var summerOffset = summer.getTimezoneOffset();
  
      // Local standard timezone offset. Local standard time is not adjusted for
      // daylight savings.  This code uses the fact that getTimezoneOffset returns
      // a greater value during Standard Time versus Daylight Saving Time (DST).
      // Thus it determines the expected output during Standard Time, and it
      // compares whether the output of the given date the same (Standard) or less
      // (DST).
      var stdTimezoneOffset = Math.max(winterOffset, summerOffset);
  
      // timezone is specified as seconds west of UTC ("The external variable
      // `timezone` shall be set to the difference, in seconds, between
      // Coordinated Universal Time (UTC) and local standard time."), the same
      // as returned by stdTimezoneOffset.
      // See http://pubs.opengroup.org/onlinepubs/009695399/functions/tzset.html
      HEAPU32[((timezone)>>2)] = stdTimezoneOffset * 60;
  
      HEAP32[((daylight)>>2)] = Number(winterOffset != summerOffset);
  
      var extractZone = (timezoneOffset) => {
        // Why inverse sign?
        // Read here https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Date/getTimezoneOffset
        var sign = timezoneOffset >= 0 ? "-" : "+";
  
        var absOffset = Math.abs(timezoneOffset)
        var hours = String(Math.floor(absOffset / 60)).padStart(2, "0");
        var minutes = String(absOffset % 60).padStart(2, "0");
  
        return `UTC${sign}${hours}${minutes}`;
      }
  
      var winterName = extractZone(winterOffset);
      var summerName = extractZone(summerOffset);
      assert(winterName);
      assert(summerName);
      assert(lengthBytesUTF8(winterName) <= 16, `timezone name truncated to fit in TZNAME_MAX (${winterName})`);
      assert(lengthBytesUTF8(summerName) <= 16, `timezone name truncated to fit in TZNAME_MAX (${summerName})`);
      if (summerOffset < winterOffset) {
        // Northern hemisphere
        stringToUTF8(winterName, std_name, 17);
        stringToUTF8(summerName, dst_name, 17);
      } else {
        stringToUTF8(winterName, dst_name, 17);
        stringToUTF8(summerName, std_name, 17);
      }
    };

  
  var _emscripten_date_now = () => Date.now();
  
  var nowIsMonotonic = 1;
  
  var checkWasiClock = (clock_id) => clock_id >= 0 && clock_id <= 3;
  
  function _clock_time_get(clk_id, ignored_precision, ptime) {
    ignored_precision = bigintToI53Checked(ignored_precision);
  
  
      if (!checkWasiClock(clk_id)) {
        return 28;
      }
      var now;
      // all wasi clocks but realtime are monotonic
      if (clk_id === 0) {
        now = _emscripten_date_now();
      } else if (nowIsMonotonic) {
        now = _emscripten_get_now();
      } else {
        return 52;
      }
      // "now" is in ms, and wasi times are in ns.
      var nsec = Math.round(now * 1000 * 1000);
      HEAP64[((ptime)>>3)] = BigInt(nsec);
      return 0;
    ;
  }


  var _emscripten_err = (str) => err(UTF8ToString(str));

  var getHeapMax = () =>
      // Stay one Wasm page short of 4GB: while e.g. Chrome is able to allocate
      // full 4GB Wasm memories, the size will wrap back to 0 bytes in Wasm side
      // for any code that deals with heap sizes, which would require special
      // casing all heap size related code to treat 0 specially.
      2147483648;
  var _emscripten_get_heap_max = () => getHeapMax();


  
  
  var growMemory = (size) => {
      var oldHeapSize = wasmMemory.buffer.byteLength;
      var pages = ((size - oldHeapSize + 65535) / 65536) | 0;
      try {
        // round size grow request up to wasm page size (fixed 64KB per spec)
        wasmMemory.grow(pages); // .grow() takes a delta compared to the previous size
        updateMemoryViews();
        return 1 /*success*/;
      } catch(e) {
        err(`growMemory: Attempted to grow heap from ${oldHeapSize} bytes to ${size} bytes, but got error: ${e}`);
      }
      // implicit 0 return to save code size (caller will cast "undefined" into 0
      // anyhow)
    };
  var _emscripten_resize_heap = (requestedSize) => {
      var oldSize = HEAPU8.length;
      // With CAN_ADDRESS_2GB or MEMORY64, pointers are already unsigned.
      requestedSize >>>= 0;
      // With multithreaded builds, races can happen (another thread might increase the size
      // in between), so return a failure, and let the caller retry.
      assert(requestedSize > oldSize);
  
      // Memory resize rules:
      // 1.  Always increase heap size to at least the requested size, rounded up
      //     to next page multiple.
      // 2a. If MEMORY_GROWTH_LINEAR_STEP == -1, excessively resize the heap
      //     geometrically: increase the heap size according to
      //     MEMORY_GROWTH_GEOMETRIC_STEP factor (default +20%), At most
      //     overreserve by MEMORY_GROWTH_GEOMETRIC_CAP bytes (default 96MB).
      // 2b. If MEMORY_GROWTH_LINEAR_STEP != -1, excessively resize the heap
      //     linearly: increase the heap size by at least
      //     MEMORY_GROWTH_LINEAR_STEP bytes.
      // 3.  Max size for the heap is capped at 2048MB-WASM_PAGE_SIZE, or by
      //     MAXIMUM_MEMORY, or by ASAN limit, depending on which is smallest
      // 4.  If we were unable to allocate as much memory, it may be due to
      //     over-eager decision to excessively reserve due to (3) above.
      //     Hence if an allocation fails, cut down on the amount of excess
      //     growth, in an attempt to succeed to perform a smaller allocation.
  
      // A limit is set for how much we can grow. We should not exceed that
      // (the wasm binary specifies it, so if we tried, we'd fail anyhow).
      var maxHeapSize = getHeapMax();
      if (requestedSize > maxHeapSize) {
        err(`Cannot enlarge memory, requested ${requestedSize} bytes, but the limit is ${maxHeapSize} bytes!`);
        return false;
      }
  
      // Loop through potential heap size increases. If we attempt a too eager
      // reservation that fails, cut down on the attempted size and reserve a
      // smaller bump instead. (max 3 times, chosen somewhat arbitrarily)
      for (var cutDown = 1; cutDown <= 4; cutDown *= 2) {
        var overGrownHeapSize = oldSize * (1 + 0.2 / cutDown); // ensure geometric growth
        // but limit overreserving (default to capping at +96MB overgrowth at most)
        overGrownHeapSize = Math.min(overGrownHeapSize, requestedSize + 100663296 );
  
        var newSize = Math.min(maxHeapSize, alignMemory(Math.max(requestedSize, overGrownHeapSize), 65536));
  
        var replacement = growMemory(newSize);
        if (replacement) {
  
          return true;
        }
      }
      err(`Failed to grow the heap from ${oldSize} bytes to ${newSize} bytes, not enough memory!`);
      return false;
    };

  var ENV = {
  };
  
  var getExecutableName = () => thisProgram || './this.program';
  var getEnvStrings = () => {
      if (!getEnvStrings.strings) {
        // Default values.
        // Browser language detection #8751
        var lang = (globalThis.navigator?.language ?? 'C').replace('-', '_') + '.UTF-8';
        var env = {
          'USER': 'web_user',
          'LOGNAME': 'web_user',
          'PATH': '/',
          'PWD': '/',
          'HOME': '/home/web_user',
          'LANG': lang,
          '_': getExecutableName()
        };
        // Apply the user-provided values, if any.
        for (var x in ENV) {
          // x is a key in ENV; if ENV[x] is undefined, that means it was
          // explicitly set to be so. We allow user code to do that to
          // force variables with default values to remain unset.
          if (ENV[x] === undefined) delete env[x];
          else env[x] = ENV[x];
        }
        var strings = [];
        for (var x in env) {
          strings.push(`${x}=${env[x]}`);
        }
        getEnvStrings.strings = strings;
      }
      return getEnvStrings.strings;
    };
  
  var _environ_get = (__environ, environ_buf) => {
      var bufSize = 0;
      var envp = 0;
      for (var string of getEnvStrings()) {
        var ptr = environ_buf + bufSize;
        HEAPU32[(((__environ)+(envp))>>2)] = ptr;
        bufSize += stringToUTF8(string, ptr, Infinity) + 1;
        envp += 4;
      }
      return 0;
    };

  
  var _environ_sizes_get = (penviron_count, penviron_buf_size) => {
      var strings = getEnvStrings();
      HEAPU32[((penviron_count)>>2)] = strings.length;
      var bufSize = 0;
      for (var string of strings) {
        bufSize += lengthBytesUTF8(string) + 1;
      }
      HEAPU32[((penviron_buf_size)>>2)] = bufSize;
      return 0;
    };


  function _fd_close(fd) {
  try {
  
      var stream = SYSCALLS.getStreamFromFD(fd);
      FS.close(stream);
      return 0;
    } catch (e) {
    if (typeof FS == 'undefined' || !(e.name === 'ErrnoError')) throw e;
    return e.errno;
  }
  }

  function _fd_fdstat_get(fd, pbuf) {
  try {
  
      var rightsBase = 0;
      var rightsInheriting = 0;
      var flags = 0;
      {
        var stream = SYSCALLS.getStreamFromFD(fd);
        // All character devices are terminals (other things a Linux system would
        // assume is a character device, like the mouse, we have special APIs for).
        var type = stream.tty ? 2 :
                   FS.isDir(stream.mode) ? 3 :
                   FS.isLink(stream.mode) ? 7 :
                   4;
      }
      HEAP8[pbuf] = type;
      HEAP16[(((pbuf)+(2))>>1)] = flags;
      HEAP64[(((pbuf)+(8))>>3)] = BigInt(rightsBase);
      HEAP64[(((pbuf)+(16))>>3)] = BigInt(rightsInheriting);
      return 0;
    } catch (e) {
    if (typeof FS == 'undefined' || !(e.name === 'ErrnoError')) throw e;
    return e.errno;
  }
  }

  /** @param {number=} offset */
  var doReadv = (stream, iov, iovcnt, offset) => {
      var ret = 0;
      for (var i = 0; i < iovcnt; i++) {
        var ptr = HEAPU32[((iov)>>2)];
        var len = HEAPU32[(((iov)+(4))>>2)];
        iov += 8;
        var curr = FS.read(stream, HEAP8, ptr, len, offset);
        if (curr < 0) return -1;
        ret += curr;
        if (curr < len) break; // nothing more to read
        if (typeof offset != 'undefined') {
          offset += curr;
        }
      }
      return ret;
    };
  
  
  function _fd_pread(fd, iov, iovcnt, offset, pnum) {
    offset = bigintToI53Checked(offset);
  
  
  try {
  
      if (isNaN(offset)) return 61;
      var stream = SYSCALLS.getStreamFromFD(fd)
      var num = doReadv(stream, iov, iovcnt, offset);
      HEAPU32[((pnum)>>2)] = num;
      return 0;
    } catch (e) {
    if (typeof FS == 'undefined' || !(e.name === 'ErrnoError')) throw e;
    return e.errno;
  }
  ;
  }

  
  function _fd_read(fd, iov, iovcnt, pnum) {
  try {
  
      var stream = SYSCALLS.getStreamFromFD(fd);
      var num = doReadv(stream, iov, iovcnt);
      HEAPU32[((pnum)>>2)] = num;
      return 0;
    } catch (e) {
    if (typeof FS == 'undefined' || !(e.name === 'ErrnoError')) throw e;
    return e.errno;
  }
  }

  
  function _fd_seek(fd, offset, whence, newOffset) {
    offset = bigintToI53Checked(offset);
  
  
  try {
  
      if (isNaN(offset)) return 61;
      var stream = SYSCALLS.getStreamFromFD(fd);
      FS.llseek(stream, offset, whence);
      HEAP64[((newOffset)>>3)] = BigInt(stream.position);
      if (stream.getdents && offset === 0 && whence === 0) stream.getdents = null; // reset readdir state
      return 0;
    } catch (e) {
    if (typeof FS == 'undefined' || !(e.name === 'ErrnoError')) throw e;
    return e.errno;
  }
  ;
  }

  /** @param {number=} offset */
  var doWritev = (stream, iov, iovcnt, offset) => {
      var ret = 0;
      for (var i = 0; i < iovcnt; i++) {
        var ptr = HEAPU32[((iov)>>2)];
        var len = HEAPU32[(((iov)+(4))>>2)];
        iov += 8;
        var curr = FS.write(stream, HEAP8, ptr, len, offset);
        if (curr < 0) return -1;
        ret += curr;
        if (curr < len) {
          // No more space to write.
          break;
        }
        if (typeof offset != 'undefined') {
          offset += curr;
        }
      }
      return ret;
    };
  
  function _fd_write(fd, iov, iovcnt, pnum) {
  try {
  
      var stream = SYSCALLS.getStreamFromFD(fd);
      var num = doWritev(stream, iov, iovcnt);
      HEAPU32[((pnum)>>2)] = num;
      return 0;
    } catch (e) {
    if (typeof FS == 'undefined' || !(e.name === 'ErrnoError')) throw e;
    return e.errno;
  }
  }


  function _random_get(buffer, size) {
  try {
  
      randomFill(HEAPU8.subarray(buffer, buffer + size));
      return 0;
    } catch (e) {
    if (typeof FS == 'undefined' || !(e.name === 'ErrnoError')) throw e;
    return e.errno;
  }
  }



  
  var updateTableMap = (offset, count) => {
      if (functionsInTableMap) {
        for (var i = offset; i < offset + count; i++) {
          var item = getWasmTableEntry(i);
          // Ignore null values.
          if (item) {
            functionsInTableMap.set(item, i);
          }
        }
      }
    };
  
  var functionsInTableMap;
  
  var getFunctionAddress = (func) => {
      // First, create the map if this is the first use.
      if (!functionsInTableMap) {
        functionsInTableMap = new WeakMap();
        updateTableMap(0, wasmTable.length);
      }
      return functionsInTableMap.get(func) || 0;
    };
  
  
  var freeTableIndexes = [];
  
  var getEmptyTableSlot = () => {
      // Reuse a free index if there is one, otherwise grow.
      if (freeTableIndexes.length) {
        return freeTableIndexes.pop();
      }
      try {
        // Grow the table
        return wasmTable['grow'](1);
      } catch (err) {
        if (!(err instanceof RangeError)) {
          throw err;
        }
        abort('Unable to grow wasm table. Set ALLOW_TABLE_GROWTH.');
      }
    };
  
  
  var setWasmTableEntry = (idx, func) => {
      /** @suppress {checkTypes} */
      wasmTable.set(idx, func);
      // With ABORT_ON_WASM_EXCEPTIONS wasmTable.get is overridden to return wrapped
      // functions so we need to call it here to retrieve the potential wrapper correctly
      // instead of just storing 'func' directly into wasmTableMirror
      /** @suppress {checkTypes} */
      wasmTableMirror[idx] = wasmTable.get(idx);
    };
  
  var uleb128EncodeWithLen = (arr) => {
      const n = arr.length;
      assert(n < 16384);
      // Note: this LEB128 length encoding produces extra byte for n < 128,
      // but we don't care as it's only used in a temporary representation.
      return [(n % 128) | 128, n >> 7, ...arr];
    };
  
  
  var wasmTypeCodes = {
      'i': 0x7f, // i32
      'p': 0x7f, // i32
      'j': 0x7e, // i64
      'f': 0x7d, // f32
      'd': 0x7c, // f64
      'e': 0x6f, // externref
    };
  var generateTypePack = (types) => uleb128EncodeWithLen(Array.from(types, (type) => {
      var code = wasmTypeCodes[type];
      assert(code, `invalid signature char: ${type}`);
      return code;
    }));
  var convertJsFunctionToWasm = (func, sig) => {
  
      // Rest of the module is static
      var bytes = Uint8Array.of(
        0x00, 0x61, 0x73, 0x6d, // magic ("\0asm")
        0x01, 0x00, 0x00, 0x00, // version: 1
        0x01, // Type section code
          // The module is static, with the exception of the type section, which is
          // generated based on the signature passed in.
          ...uleb128EncodeWithLen([
            0x01, // count: 1
            0x60 /* form: func */,
            // param types
            ...generateTypePack(sig.slice(1)),
            // return types (for now only supporting [] if `void` and single [T] otherwise)
            ...generateTypePack(sig[0] === 'v' ? '' : sig[0])
          ]),
        // The rest of the module is static
        0x02, 0x07, // import section
          // (import "e" "f" (func 0 (type 0)))
          0x01, 0x01, 0x65, 0x01, 0x66, 0x00, 0x00,
        0x07, 0x05, // export section
          // (export "f" (func 0 (type 0)))
          0x01, 0x01, 0x66, 0x00, 0x00,
      );
  
      // We can compile this wasm module synchronously because it is very small.
      // This accepts an import (at "e.f"), that it reroutes to an export (at "f")
      var module = new WebAssembly.Module(bytes);
      var instance = new WebAssembly.Instance(module, { 'e': { 'f': func } });
      var wrappedFunc = instance.exports['f'];
      return wrappedFunc;
    };
  /** @param {string=} sig */
  var addFunction = (func, sig) => {
      assert(typeof func != 'undefined');
      // Check if the function is already in the table, to ensure each function
      // gets a unique index.
      var rtn = getFunctionAddress(func);
      if (rtn) {
        return rtn;
      }
  
      // It's not in the table, add it now.
  
      var ret = getEmptyTableSlot();
  
      // Set the new value.
      try {
        // Attempting to call this with JS function will cause of table.set() to fail
        setWasmTableEntry(ret, func);
      } catch (err) {
        if (!(err instanceof TypeError)) {
          throw err;
        }
        assert(typeof sig != 'undefined', 'Missing signature argument to addFunction: ' + func);
        var wrapped = convertJsFunctionToWasm(func, sig);
        setWasmTableEntry(ret, wrapped);
      }
  
      functionsInTableMap.set(func, ret);
  
      return ret;
    };

  
  
  
  
  var removeFunction = (index) => {
      functionsInTableMap.delete(getWasmTableEntry(index));
      setWasmTableEntry(index, null);
      freeTableIndexes.push(index);
    };

  var getCFunc = (ident) => {
      var func = Module['_' + ident]; // closure exported function
      assert(func, 'Cannot call unknown function ' + ident + ', make sure it is exported');
      return func;
    };
  
  var writeArrayToMemory = (array, buffer) => {
      assert(array.length >= 0, 'writeArrayToMemory array must have a length (should be an array or typed array)')
      HEAP8.set(array, buffer);
    };
  
  
  
  var stackAlloc = (sz) => __emscripten_stack_alloc(sz);
  var stringToUTF8OnStack = (str) => {
      var size = lengthBytesUTF8(str) + 1;
      var ret = stackAlloc(size);
      stringToUTF8(str, ret, size);
      return ret;
    };
  
  
  
  
  
    /**
     * @param {string|null=} returnType
     * @param {Array=} argTypes
     * @param {Array=} args
     * @param {Object=} opts
     */
  var ccall = (ident, returnType, argTypes, args, opts) => {
      // For fast lookup of conversion functions
      var toC = {
        'string': (str) => {
          var ret = 0;
          if (str !== null && str !== undefined && str !== 0) { // null string
            ret = stringToUTF8OnStack(str);
          }
          return ret;
        },
        'array': (arr) => {
          var ret = stackAlloc(arr.length);
          writeArrayToMemory(arr, ret);
          return ret;
        }
      };
  
      function convertReturnValue(ret) {
        if (returnType === 'string') {
          return UTF8ToString(ret);
        }
        if (returnType === 'boolean') return Boolean(ret);
        return ret;
      }
  
      var func = getCFunc(ident);
      var cArgs = [];
      var stack = 0;
      assert(returnType !== 'array', 'Return type should not be "array".');
      if (args) {
        for (var i = 0; i < args.length; i++) {
          var converter = toC[argTypes[i]];
          if (converter) {
            if (stack === 0) stack = stackSave();
            cArgs[i] = converter(args[i]);
          } else {
            cArgs[i] = args[i];
          }
        }
      }
      var ret = func(...cArgs);
      function onDone(ret) {
        if (stack !== 0) stackRestore(stack);
        return convertReturnValue(ret);
      }
  
      ret = onDone(ret);
      return ret;
    };
  
    /**
     * @param {string=} returnType
     * @param {Array=} argTypes
     * @param {Object=} opts
     */
  var cwrap = (ident, returnType, argTypes, opts) => {
      return (...args) => ccall(ident, returnType, argTypes, args, opts);
    };







  FS.createPreloadedFile = FS_createPreloadedFile;
  FS.preloadFile = FS_preloadFile;
  FS.staticInit();;
// End JS library code

// include: postlibrary.js
// This file is included after the automatically-generated JS library code
// but before the wasm module is created.

{

  // Begin ATMODULES hooks
  if (Module['noExitRuntime']) noExitRuntime = Module['noExitRuntime'];
if (Module['preloadPlugins']) preloadPlugins = Module['preloadPlugins'];
if (Module['print']) out = Module['print'];
if (Module['printErr']) err = Module['printErr'];
if (Module['wasmBinary']) wasmBinary = Module['wasmBinary'];
  // End ATMODULES hooks

  checkIncomingModuleAPI();

  if (Module['arguments']) arguments_ = Module['arguments'];
  if (Module['thisProgram']) thisProgram = Module['thisProgram'];

  // Assertions on removed incoming Module JS APIs.
  assert(typeof Module['memoryInitializerPrefixURL'] == 'undefined', 'Module.memoryInitializerPrefixURL option was removed, use Module.locateFile instead');
  assert(typeof Module['pthreadMainPrefixURL'] == 'undefined', 'Module.pthreadMainPrefixURL option was removed, use Module.locateFile instead');
  assert(typeof Module['cdInitializerPrefixURL'] == 'undefined', 'Module.cdInitializerPrefixURL option was removed, use Module.locateFile instead');
  assert(typeof Module['filePackagePrefixURL'] == 'undefined', 'Module.filePackagePrefixURL option was removed, use Module.locateFile instead');
  assert(typeof Module['read'] == 'undefined', 'Module.read option was removed');
  assert(typeof Module['readAsync'] == 'undefined', 'Module.readAsync option was removed (modify readAsync in JS)');
  assert(typeof Module['readBinary'] == 'undefined', 'Module.readBinary option was removed (modify readBinary in JS)');
  assert(typeof Module['setWindowTitle'] == 'undefined', 'Module.setWindowTitle option was removed (modify emscripten_set_window_title in JS)');
  assert(typeof Module['TOTAL_MEMORY'] == 'undefined', 'Module.TOTAL_MEMORY has been renamed Module.INITIAL_MEMORY');
  assert(typeof Module['ENVIRONMENT'] == 'undefined', 'Module.ENVIRONMENT has been deprecated. To force the environment, use the ENVIRONMENT compile-time option (for example, -sENVIRONMENT=web or -sENVIRONMENT=node)');
  assert(typeof Module['STACK_SIZE'] == 'undefined', 'STACK_SIZE can no longer be set at runtime.  Use -sSTACK_SIZE at link time')
  // If memory is defined in wasm, the user can't provide it, or set INITIAL_MEMORY
  assert(typeof Module['wasmMemory'] == 'undefined', 'Use of `wasmMemory` detected.  Use -sIMPORTED_MEMORY to define wasmMemory externally');
  assert(typeof Module['INITIAL_MEMORY'] == 'undefined', 'Detected runtime INITIAL_MEMORY setting.  Use -sIMPORTED_MEMORY to define wasmMemory dynamically');

  if (Module['preInit']) {
    if (typeof Module['preInit'] == 'function') Module['preInit'] = [Module['preInit']];
    while (Module['preInit'].length > 0) {
      Module['preInit'].shift()();
    }
  }
  consumedModuleProp('preInit');
}

// Begin runtime exports
  Module['wasmExports'] = wasmExports;
  Module['ccall'] = ccall;
  Module['cwrap'] = cwrap;
  Module['addFunction'] = addFunction;
  Module['removeFunction'] = removeFunction;
  Module['setValue'] = setValue;
  Module['getValue'] = getValue;
  Module['UTF8ToString'] = UTF8ToString;
  Module['stringToUTF8'] = stringToUTF8;
  Module['lengthBytesUTF8'] = lengthBytesUTF8;
  Module['FS'] = FS;
  var missingLibrarySymbols = [
  'writeI53ToI64',
  'writeI53ToI64Clamped',
  'writeI53ToI64Signaling',
  'writeI53ToU64Clamped',
  'writeI53ToU64Signaling',
  'readI53FromI64',
  'readI53FromU64',
  'convertI32PairToI53',
  'convertI32PairToI53Checked',
  'convertU32PairToI53',
  'getTempRet0',
  'setTempRet0',
  'createNamedFunction',
  'withStackSave',
  'inetPton4',
  'inetNtop4',
  'inetPton6',
  'inetNtop6',
  'readSockaddr',
  'writeSockaddr',
  'readEmAsmArgs',
  'jstoi_q',
  'autoResumeAudioContext',
  'getDynCaller',
  'dynCall',
  'runtimeKeepalivePush',
  'runtimeKeepalivePop',
  'asmjsMangle',
  'HandleAllocator',
  'addOnInit',
  'addOnPostCtor',
  'addOnPreMain',
  'addOnExit',
  'STACK_SIZE',
  'STACK_ALIGN',
  'POINTER_SIZE',
  'ASSERTIONS',
  'intArrayToString',
  'AsciiToString',
  'stringToAscii',
  'UTF16ToString',
  'stringToUTF16',
  'lengthBytesUTF16',
  'UTF32ToString',
  'stringToUTF32',
  'lengthBytesUTF32',
  'stringToNewUTF8',
  'registerKeyEventCallback',
  'maybeCStringToJsString',
  'findEventTarget',
  'getBoundingClientRect',
  'fillMouseEventData',
  'registerMouseEventCallback',
  'registerWheelEventCallback',
  'registerUiEventCallback',
  'registerFocusEventCallback',
  'fillDeviceOrientationEventData',
  'registerDeviceOrientationEventCallback',
  'fillDeviceMotionEventData',
  'registerDeviceMotionEventCallback',
  'screenOrientation',
  'fillOrientationChangeEventData',
  'registerOrientationChangeEventCallback',
  'fillFullscreenChangeEventData',
  'registerFullscreenChangeEventCallback',
  'JSEvents_requestFullscreen',
  'JSEvents_resizeCanvasForFullscreen',
  'registerRestoreOldStyle',
  'hideEverythingExceptGivenElement',
  'restoreHiddenElements',
  'setLetterbox',
  'softFullscreenResizeWebGLRenderTarget',
  'doRequestFullscreen',
  'fillPointerlockChangeEventData',
  'registerPointerlockChangeEventCallback',
  'registerPointerlockErrorEventCallback',
  'requestPointerLock',
  'fillVisibilityChangeEventData',
  'registerVisibilityChangeEventCallback',
  'registerTouchEventCallback',
  'fillGamepadEventData',
  'registerGamepadEventCallback',
  'registerBeforeUnloadEventCallback',
  'fillBatteryEventData',
  'registerBatteryEventCallback',
  'setCanvasElementSize',
  'getCanvasElementSize',
  'jsStackTrace',
  'getCallstack',
  'convertPCtoSourceLocation',
  'wasiRightsToMuslOFlags',
  'wasiOFlagsToMuslOFlags',
  'safeSetTimeout',
  'setImmediateWrapped',
  'safeRequestAnimationFrame',
  'clearImmediateWrapped',
  'registerPostMainLoop',
  'registerPreMainLoop',
  'getPromise',
  'makePromise',
  'idsToPromises',
  'makePromiseCallback',
  'findMatchingCatch',
  'Browser_asyncPrepareDataCounter',
  'arraySum',
  'addDays',
  'getSocketFromFD',
  'getSocketAddress',
  'FS_mkdirTree',
  '_setNetworkCallback',
  'heapObjectForWebGLType',
  'toTypedArrayIndex',
  'webgl_enable_ANGLE_instanced_arrays',
  'webgl_enable_OES_vertex_array_object',
  'webgl_enable_WEBGL_draw_buffers',
  'webgl_enable_WEBGL_multi_draw',
  'webgl_enable_EXT_polygon_offset_clamp',
  'webgl_enable_EXT_clip_control',
  'webgl_enable_WEBGL_polygon_mode',
  'emscriptenWebGLGet',
  'computeUnpackAlignedImageSize',
  'colorChannelsInGlTextureFormat',
  'emscriptenWebGLGetTexPixelData',
  'emscriptenWebGLGetUniform',
  'webglGetUniformLocation',
  'webglPrepareUniformLocationsBeforeFirstUse',
  'webglGetLeftBracePos',
  'emscriptenWebGLGetVertexAttrib',
  '__glGetActiveAttribOrUniform',
  'writeGLArray',
  'registerWebGlEventCallback',
  'runAndAbortIfError',
  'ALLOC_NORMAL',
  'ALLOC_STACK',
  'allocate',
  'writeStringToMemory',
  'writeAsciiToMemory',
  'allocateUTF8',
  'allocateUTF8OnStack',
  'demangle',
  'stackTrace',
  'getNativeTypeSize',
];
missingLibrarySymbols.forEach(missingLibrarySymbol)

  var unexportedSymbols = [
  'run',
  'out',
  'err',
  'callMain',
  'abort',
  'HEAPF32',
  'HEAPF64',
  'HEAP8',
  'HEAPU8',
  'HEAP16',
  'HEAPU16',
  'HEAP32',
  'HEAPU32',
  'HEAP64',
  'HEAPU64',
  'writeStackCookie',
  'checkStackCookie',
  'INT53_MAX',
  'INT53_MIN',
  'bigintToI53Checked',
  'stackSave',
  'stackRestore',
  'stackAlloc',
  'ptrToString',
  'zeroMemory',
  'exitJS',
  'getHeapMax',
  'growMemory',
  'ENV',
  'ERRNO_CODES',
  'strError',
  'DNS',
  'Protocols',
  'Sockets',
  'timers',
  'warnOnce',
  'readEmAsmArgsArray',
  'getExecutableName',
  'handleException',
  'keepRuntimeAlive',
  'callUserCallback',
  'maybeExit',
  'asyncLoad',
  'alignMemory',
  'mmapAlloc',
  'wasmTable',
  'wasmMemory',
  'getUniqueRunDependency',
  'noExitRuntime',
  'addRunDependency',
  'removeRunDependency',
  'addOnPreRun',
  'addOnPostRun',
  'convertJsFunctionToWasm',
  'freeTableIndexes',
  'functionsInTableMap',
  'getEmptyTableSlot',
  'updateTableMap',
  'getFunctionAddress',
  'PATH',
  'PATH_FS',
  'UTF8Decoder',
  'UTF8ArrayToString',
  'stringToUTF8Array',
  'intArrayFromString',
  'UTF16Decoder',
  'stringToUTF8OnStack',
  'writeArrayToMemory',
  'JSEvents',
  'specialHTMLTargets',
  'findCanvasEventTarget',
  'currentFullscreenStrategy',
  'restoreOldWindowedStyle',
  'UNWIND_CACHE',
  'ExitStatus',
  'getEnvStrings',
  'checkWasiClock',
  'doReadv',
  'doWritev',
  'initRandomFill',
  'randomFill',
  'emSetImmediate',
  'emClearImmediate_deps',
  'emClearImmediate',
  'promiseMap',
  'uncaughtExceptionCount',
  'exceptionLast',
  'exceptionCaught',
  'ExceptionInfo',
  'Browser',
  'requestFullscreen',
  'requestFullScreen',
  'setCanvasSize',
  'getUserMedia',
  'createContext',
  'getPreloadedImageData__data',
  'wget',
  'MONTH_DAYS_REGULAR',
  'MONTH_DAYS_LEAP',
  'MONTH_DAYS_REGULAR_CUMULATIVE',
  'MONTH_DAYS_LEAP_CUMULATIVE',
  'isLeapYear',
  'ydayFromDate',
  'SYSCALLS',
  'preloadPlugins',
  'FS_createPreloadedFile',
  'FS_preloadFile',
  'FS_modeStringToFlags',
  'FS_getMode',
  'FS_stdin_getChar_buffer',
  'FS_stdin_getChar',
  'FS_unlink',
  'FS_createPath',
  'FS_createDevice',
  'FS_readFile',
  'FS_root',
  'FS_mounts',
  'FS_devices',
  'FS_streams',
  'FS_nextInode',
  'FS_nameTable',
  'FS_currentPath',
  'FS_initialized',
  'FS_ignorePermissions',
  'FS_filesystems',
  'FS_syncFSRequests',
  'FS_readFiles',
  'FS_lookupPath',
  'FS_getPath',
  'FS_hashName',
  'FS_hashAddNode',
  'FS_hashRemoveNode',
  'FS_lookupNode',
  'FS_createNode',
  'FS_destroyNode',
  'FS_isRoot',
  'FS_isMountpoint',
  'FS_isFile',
  'FS_isDir',
  'FS_isLink',
  'FS_isChrdev',
  'FS_isBlkdev',
  'FS_isFIFO',
  'FS_isSocket',
  'FS_flagsToPermissionString',
  'FS_nodePermissions',
  'FS_mayLookup',
  'FS_mayCreate',
  'FS_mayDelete',
  'FS_mayOpen',
  'FS_checkOpExists',
  'FS_nextfd',
  'FS_getStreamChecked',
  'FS_getStream',
  'FS_createStream',
  'FS_closeStream',
  'FS_dupStream',
  'FS_doSetAttr',
  'FS_chrdev_stream_ops',
  'FS_major',
  'FS_minor',
  'FS_makedev',
  'FS_registerDevice',
  'FS_getDevice',
  'FS_getMounts',
  'FS_syncfs',
  'FS_mount',
  'FS_unmount',
  'FS_lookup',
  'FS_mknod',
  'FS_statfs',
  'FS_statfsStream',
  'FS_statfsNode',
  'FS_create',
  'FS_mkdir',
  'FS_mkdev',
  'FS_symlink',
  'FS_rename',
  'FS_rmdir',
  'FS_readdir',
  'FS_readlink',
  'FS_stat',
  'FS_fstat',
  'FS_lstat',
  'FS_doChmod',
  'FS_chmod',
  'FS_lchmod',
  'FS_fchmod',
  'FS_doChown',
  'FS_chown',
  'FS_lchown',
  'FS_fchown',
  'FS_doTruncate',
  'FS_truncate',
  'FS_ftruncate',
  'FS_utime',
  'FS_open',
  'FS_close',
  'FS_isClosed',
  'FS_llseek',
  'FS_read',
  'FS_write',
  'FS_mmap',
  'FS_msync',
  'FS_ioctl',
  'FS_writeFile',
  'FS_cwd',
  'FS_chdir',
  'FS_createDefaultDirectories',
  'FS_createDefaultDevices',
  'FS_createSpecialDirectories',
  'FS_createStandardStreams',
  'FS_staticInit',
  'FS_init',
  'FS_quit',
  'FS_findObject',
  'FS_analyzePath',
  'FS_createFile',
  'FS_createDataFile',
  'FS_forceLoadFile',
  'FS_createLazyFile',
  'FS_absolutePath',
  'FS_createFolder',
  'FS_createLink',
  'FS_joinPath',
  'FS_mmapAlloc',
  'FS_standardizePath',
  'MEMFS',
  'TTY',
  'PIPEFS',
  'SOCKFS',
  'tempFixedLengthArray',
  'miniTempWebGLFloatBuffers',
  'miniTempWebGLIntBuffers',
  'GL',
  'AL',
  'GLUT',
  'EGL',
  'GLEW',
  'IDBStore',
  'SDL',
  'SDL_gfx',
  'print',
  'printErr',
  'jstoi_s',
];
unexportedSymbols.forEach(unexportedRuntimeSymbol);

  // End runtime exports
  // Begin JS library exports
  // End JS library exports

// end include: postlibrary.js

function checkIncomingModuleAPI() {
  ignoredModuleProp('fetchSettings');
}

// Imports from the Wasm binary.
var _clang_getRemappings = Module['_clang_getRemappings'] = makeInvalidEarlyAccess('_clang_getRemappings');
var _clang_getRemappingsFromFileList = Module['_clang_getRemappingsFromFileList'] = makeInvalidEarlyAccess('_clang_getRemappingsFromFileList');
var _clang_remap_getNumFiles = Module['_clang_remap_getNumFiles'] = makeInvalidEarlyAccess('_clang_remap_getNumFiles');
var _clang_remap_getFilenames = Module['_clang_remap_getFilenames'] = makeInvalidEarlyAccess('_clang_remap_getFilenames');
var _clang_remap_dispose = Module['_clang_remap_dispose'] = makeInvalidEarlyAccess('_clang_remap_dispose');
var _clang_getBuildSessionTimestamp = Module['_clang_getBuildSessionTimestamp'] = makeInvalidEarlyAccess('_clang_getBuildSessionTimestamp');
var _clang_VirtualFileOverlay_create = Module['_clang_VirtualFileOverlay_create'] = makeInvalidEarlyAccess('_clang_VirtualFileOverlay_create');
var _clang_VirtualFileOverlay_addFileMapping = Module['_clang_VirtualFileOverlay_addFileMapping'] = makeInvalidEarlyAccess('_clang_VirtualFileOverlay_addFileMapping');
var _clang_VirtualFileOverlay_setCaseSensitivity = Module['_clang_VirtualFileOverlay_setCaseSensitivity'] = makeInvalidEarlyAccess('_clang_VirtualFileOverlay_setCaseSensitivity');
var _clang_VirtualFileOverlay_writeToBuffer = Module['_clang_VirtualFileOverlay_writeToBuffer'] = makeInvalidEarlyAccess('_clang_VirtualFileOverlay_writeToBuffer');
var _clang_free = Module['_clang_free'] = makeInvalidEarlyAccess('_clang_free');
var _clang_VirtualFileOverlay_dispose = Module['_clang_VirtualFileOverlay_dispose'] = makeInvalidEarlyAccess('_clang_VirtualFileOverlay_dispose');
var _clang_ModuleMapDescriptor_create = Module['_clang_ModuleMapDescriptor_create'] = makeInvalidEarlyAccess('_clang_ModuleMapDescriptor_create');
var _clang_ModuleMapDescriptor_setFrameworkModuleName = Module['_clang_ModuleMapDescriptor_setFrameworkModuleName'] = makeInvalidEarlyAccess('_clang_ModuleMapDescriptor_setFrameworkModuleName');
var _clang_ModuleMapDescriptor_setUmbrellaHeader = Module['_clang_ModuleMapDescriptor_setUmbrellaHeader'] = makeInvalidEarlyAccess('_clang_ModuleMapDescriptor_setUmbrellaHeader');
var _clang_ModuleMapDescriptor_writeToBuffer = Module['_clang_ModuleMapDescriptor_writeToBuffer'] = makeInvalidEarlyAccess('_clang_ModuleMapDescriptor_writeToBuffer');
var _clang_ModuleMapDescriptor_dispose = Module['_clang_ModuleMapDescriptor_dispose'] = makeInvalidEarlyAccess('_clang_ModuleMapDescriptor_dispose');
var _clang_disposeTranslationUnit = Module['_clang_disposeTranslationUnit'] = makeInvalidEarlyAccess('_clang_disposeTranslationUnit');
var _clang_isInvalid = Module['_clang_isInvalid'] = makeInvalidEarlyAccess('_clang_isInvalid');
var _clang_isDeclaration = Module['_clang_isDeclaration'] = makeInvalidEarlyAccess('_clang_isDeclaration');
var _clang_isReference = Module['_clang_isReference'] = makeInvalidEarlyAccess('_clang_isReference');
var _clang_isStatement = Module['_clang_isStatement'] = makeInvalidEarlyAccess('_clang_isStatement');
var _clang_isExpression = Module['_clang_isExpression'] = makeInvalidEarlyAccess('_clang_isExpression');
var _clang_isTranslationUnit = Module['_clang_isTranslationUnit'] = makeInvalidEarlyAccess('_clang_isTranslationUnit');
var _clang_createIndex = Module['_clang_createIndex'] = makeInvalidEarlyAccess('_clang_createIndex');
var _clang_disposeIndex = Module['_clang_disposeIndex'] = makeInvalidEarlyAccess('_clang_disposeIndex');
var _clang_CXIndex_setGlobalOptions = Module['_clang_CXIndex_setGlobalOptions'] = makeInvalidEarlyAccess('_clang_CXIndex_setGlobalOptions');
var _clang_CXIndex_getGlobalOptions = Module['_clang_CXIndex_getGlobalOptions'] = makeInvalidEarlyAccess('_clang_CXIndex_getGlobalOptions');
var _clang_CXIndex_setInvocationEmissionPathOption = Module['_clang_CXIndex_setInvocationEmissionPathOption'] = makeInvalidEarlyAccess('_clang_CXIndex_setInvocationEmissionPathOption');
var _clang_toggleCrashRecovery = Module['_clang_toggleCrashRecovery'] = makeInvalidEarlyAccess('_clang_toggleCrashRecovery');
var _clang_createTranslationUnit = Module['_clang_createTranslationUnit'] = makeInvalidEarlyAccess('_clang_createTranslationUnit');
var _clang_createTranslationUnit2 = Module['_clang_createTranslationUnit2'] = makeInvalidEarlyAccess('_clang_createTranslationUnit2');
var _clang_defaultEditingTranslationUnitOptions = Module['_clang_defaultEditingTranslationUnitOptions'] = makeInvalidEarlyAccess('_clang_defaultEditingTranslationUnitOptions');
var _clang_createTranslationUnitFromSourceFile = Module['_clang_createTranslationUnitFromSourceFile'] = makeInvalidEarlyAccess('_clang_createTranslationUnitFromSourceFile');
var _clang_parseTranslationUnit2 = Module['_clang_parseTranslationUnit2'] = makeInvalidEarlyAccess('_clang_parseTranslationUnit2');
var _clang_parseTranslationUnit = Module['_clang_parseTranslationUnit'] = makeInvalidEarlyAccess('_clang_parseTranslationUnit');
var _clang_parseTranslationUnit2FullArgv = Module['_clang_parseTranslationUnit2FullArgv'] = makeInvalidEarlyAccess('_clang_parseTranslationUnit2FullArgv');
var _clang_getCXTUResourceUsage = Module['_clang_getCXTUResourceUsage'] = makeInvalidEarlyAccess('_clang_getCXTUResourceUsage');
var _clang_getTUResourceUsageName = Module['_clang_getTUResourceUsageName'] = makeInvalidEarlyAccess('_clang_getTUResourceUsageName');
var _clang_disposeCXTUResourceUsage = Module['_clang_disposeCXTUResourceUsage'] = makeInvalidEarlyAccess('_clang_disposeCXTUResourceUsage');
var _clang_Type_getObjCEncoding = Module['_clang_Type_getObjCEncoding'] = makeInvalidEarlyAccess('_clang_Type_getObjCEncoding');
var _clang_Cursor_isMacroFunctionLike = Module['_clang_Cursor_isMacroFunctionLike'] = makeInvalidEarlyAccess('_clang_Cursor_isMacroFunctionLike');
var _clang_Cursor_isMacroBuiltin = Module['_clang_Cursor_isMacroBuiltin'] = makeInvalidEarlyAccess('_clang_Cursor_isMacroBuiltin');
var _clang_Cursor_isFunctionInlined = Module['_clang_Cursor_isFunctionInlined'] = makeInvalidEarlyAccess('_clang_Cursor_isFunctionInlined');
var _clang_EvalResult_dispose = Module['_clang_EvalResult_dispose'] = makeInvalidEarlyAccess('_clang_EvalResult_dispose');
var _clang_EvalResult_getKind = Module['_clang_EvalResult_getKind'] = makeInvalidEarlyAccess('_clang_EvalResult_getKind');
var _clang_EvalResult_getAsInt = Module['_clang_EvalResult_getAsInt'] = makeInvalidEarlyAccess('_clang_EvalResult_getAsInt');
var _clang_EvalResult_getAsLongLong = Module['_clang_EvalResult_getAsLongLong'] = makeInvalidEarlyAccess('_clang_EvalResult_getAsLongLong');
var _clang_EvalResult_isUnsignedInt = Module['_clang_EvalResult_isUnsignedInt'] = makeInvalidEarlyAccess('_clang_EvalResult_isUnsignedInt');
var _clang_EvalResult_getAsUnsigned = Module['_clang_EvalResult_getAsUnsigned'] = makeInvalidEarlyAccess('_clang_EvalResult_getAsUnsigned');
var _clang_EvalResult_getAsDouble = Module['_clang_EvalResult_getAsDouble'] = makeInvalidEarlyAccess('_clang_EvalResult_getAsDouble');
var _clang_EvalResult_getAsStr = Module['_clang_EvalResult_getAsStr'] = makeInvalidEarlyAccess('_clang_EvalResult_getAsStr');
var _clang_Cursor_Evaluate = Module['_clang_Cursor_Evaluate'] = makeInvalidEarlyAccess('_clang_Cursor_Evaluate');
var _clang_getCursorKind = Module['_clang_getCursorKind'] = makeInvalidEarlyAccess('_clang_getCursorKind');
var _clang_Cursor_hasAttrs = Module['_clang_Cursor_hasAttrs'] = makeInvalidEarlyAccess('_clang_Cursor_hasAttrs');
var _clang_defaultSaveOptions = Module['_clang_defaultSaveOptions'] = makeInvalidEarlyAccess('_clang_defaultSaveOptions');
var _clang_saveTranslationUnit = Module['_clang_saveTranslationUnit'] = makeInvalidEarlyAccess('_clang_saveTranslationUnit');
var _clang_suspendTranslationUnit = Module['_clang_suspendTranslationUnit'] = makeInvalidEarlyAccess('_clang_suspendTranslationUnit');
var _clang_defaultReparseOptions = Module['_clang_defaultReparseOptions'] = makeInvalidEarlyAccess('_clang_defaultReparseOptions');
var _clang_reparseTranslationUnit = Module['_clang_reparseTranslationUnit'] = makeInvalidEarlyAccess('_clang_reparseTranslationUnit');
var _clang_getTranslationUnitSpelling = Module['_clang_getTranslationUnitSpelling'] = makeInvalidEarlyAccess('_clang_getTranslationUnitSpelling');
var _clang_getTranslationUnitCursor = Module['_clang_getTranslationUnitCursor'] = makeInvalidEarlyAccess('_clang_getTranslationUnitCursor');
var _clang_getNullCursor = Module['_clang_getNullCursor'] = makeInvalidEarlyAccess('_clang_getNullCursor');
var _clang_getTranslationUnitTargetInfo = Module['_clang_getTranslationUnitTargetInfo'] = makeInvalidEarlyAccess('_clang_getTranslationUnitTargetInfo');
var _clang_TargetInfo_getTriple = Module['_clang_TargetInfo_getTriple'] = makeInvalidEarlyAccess('_clang_TargetInfo_getTriple');
var _clang_TargetInfo_getPointerWidth = Module['_clang_TargetInfo_getPointerWidth'] = makeInvalidEarlyAccess('_clang_TargetInfo_getPointerWidth');
var _clang_TargetInfo_dispose = Module['_clang_TargetInfo_dispose'] = makeInvalidEarlyAccess('_clang_TargetInfo_dispose');
var _clang_getFileName = Module['_clang_getFileName'] = makeInvalidEarlyAccess('_clang_getFileName');
var _clang_getFileTime = Module['_clang_getFileTime'] = makeInvalidEarlyAccess('_clang_getFileTime');
var _clang_getFile = Module['_clang_getFile'] = makeInvalidEarlyAccess('_clang_getFile');
var _clang_getFileContents = Module['_clang_getFileContents'] = makeInvalidEarlyAccess('_clang_getFileContents');
var _clang_isFileMultipleIncludeGuarded = Module['_clang_isFileMultipleIncludeGuarded'] = makeInvalidEarlyAccess('_clang_isFileMultipleIncludeGuarded');
var _clang_getFileUniqueID = Module['_clang_getFileUniqueID'] = makeInvalidEarlyAccess('_clang_getFileUniqueID');
var _clang_File_isEqual = Module['_clang_File_isEqual'] = makeInvalidEarlyAccess('_clang_File_isEqual');
var _clang_File_tryGetRealPathName = Module['_clang_File_tryGetRealPathName'] = makeInvalidEarlyAccess('_clang_File_tryGetRealPathName');
var _clang_visitChildren = Module['_clang_visitChildren'] = makeInvalidEarlyAccess('_clang_visitChildren');
var _clang_visitChildrenWithBlock = Module['_clang_visitChildrenWithBlock'] = makeInvalidEarlyAccess('_clang_visitChildrenWithBlock');
var _clang_getCursorSpelling = Module['_clang_getCursorSpelling'] = makeInvalidEarlyAccess('_clang_getCursorSpelling');
var _clang_Cursor_getSpellingNameRange = Module['_clang_Cursor_getSpellingNameRange'] = makeInvalidEarlyAccess('_clang_Cursor_getSpellingNameRange');
var _clang_getCursorLocation = Module['_clang_getCursorLocation'] = makeInvalidEarlyAccess('_clang_getCursorLocation');
var _clang_Cursor_getMangling = Module['_clang_Cursor_getMangling'] = makeInvalidEarlyAccess('_clang_Cursor_getMangling');
var _clang_Cursor_getCXXManglings = Module['_clang_Cursor_getCXXManglings'] = makeInvalidEarlyAccess('_clang_Cursor_getCXXManglings');
var _clang_Cursor_getObjCManglings = Module['_clang_Cursor_getObjCManglings'] = makeInvalidEarlyAccess('_clang_Cursor_getObjCManglings');
var _clang_getCursorPrintingPolicy = Module['_clang_getCursorPrintingPolicy'] = makeInvalidEarlyAccess('_clang_getCursorPrintingPolicy');
var _clang_PrintingPolicy_dispose = Module['_clang_PrintingPolicy_dispose'] = makeInvalidEarlyAccess('_clang_PrintingPolicy_dispose');
var _clang_PrintingPolicy_getProperty = Module['_clang_PrintingPolicy_getProperty'] = makeInvalidEarlyAccess('_clang_PrintingPolicy_getProperty');
var _clang_PrintingPolicy_setProperty = Module['_clang_PrintingPolicy_setProperty'] = makeInvalidEarlyAccess('_clang_PrintingPolicy_setProperty');
var _clang_getCursorPrettyPrinted = Module['_clang_getCursorPrettyPrinted'] = makeInvalidEarlyAccess('_clang_getCursorPrettyPrinted');
var _clang_getCursorDisplayName = Module['_clang_getCursorDisplayName'] = makeInvalidEarlyAccess('_clang_getCursorDisplayName');
var _clang_getCursorKindSpelling = Module['_clang_getCursorKindSpelling'] = makeInvalidEarlyAccess('_clang_getCursorKindSpelling');
var _clang_getCursor = Module['_clang_getCursor'] = makeInvalidEarlyAccess('_clang_getCursor');
var _clang_getCursorDefinition = Module['_clang_getCursorDefinition'] = makeInvalidEarlyAccess('_clang_getCursorDefinition');
var _clang_isCursorDefinition = Module['_clang_isCursorDefinition'] = makeInvalidEarlyAccess('_clang_isCursorDefinition');
var _clang_getCursorReferenced = Module['_clang_getCursorReferenced'] = makeInvalidEarlyAccess('_clang_getCursorReferenced');
var _clang_equalCursors = Module['_clang_equalCursors'] = makeInvalidEarlyAccess('_clang_equalCursors');
var _clang_hashCursor = Module['_clang_hashCursor'] = makeInvalidEarlyAccess('_clang_hashCursor');
var _clang_isInvalidDeclaration = Module['_clang_isInvalidDeclaration'] = makeInvalidEarlyAccess('_clang_isInvalidDeclaration');
var _clang_isAttribute = Module['_clang_isAttribute'] = makeInvalidEarlyAccess('_clang_isAttribute');
var _clang_isPreprocessing = Module['_clang_isPreprocessing'] = makeInvalidEarlyAccess('_clang_isPreprocessing');
var _clang_isUnexposed = Module['_clang_isUnexposed'] = makeInvalidEarlyAccess('_clang_isUnexposed');
var _clang_getCursorExtent = Module['_clang_getCursorExtent'] = makeInvalidEarlyAccess('_clang_getCursorExtent');
var _clang_getCanonicalCursor = Module['_clang_getCanonicalCursor'] = makeInvalidEarlyAccess('_clang_getCanonicalCursor');
var _clang_Cursor_getObjCSelectorIndex = Module['_clang_Cursor_getObjCSelectorIndex'] = makeInvalidEarlyAccess('_clang_Cursor_getObjCSelectorIndex');
var _clang_getNumOverloadedDecls = Module['_clang_getNumOverloadedDecls'] = makeInvalidEarlyAccess('_clang_getNumOverloadedDecls');
var _clang_getOverloadedDecl = Module['_clang_getOverloadedDecl'] = makeInvalidEarlyAccess('_clang_getOverloadedDecl');
var _clang_getDefinitionSpellingAndExtent = Module['_clang_getDefinitionSpellingAndExtent'] = makeInvalidEarlyAccess('_clang_getDefinitionSpellingAndExtent');
var _clang_getCursorReferenceNameRange = Module['_clang_getCursorReferenceNameRange'] = makeInvalidEarlyAccess('_clang_getCursorReferenceNameRange');
var _clang_enableStackTraces = Module['_clang_enableStackTraces'] = makeInvalidEarlyAccess('_clang_enableStackTraces');
var _clang_executeOnThread = Module['_clang_executeOnThread'] = makeInvalidEarlyAccess('_clang_executeOnThread');
var _clang_getTokenKind = Module['_clang_getTokenKind'] = makeInvalidEarlyAccess('_clang_getTokenKind');
var _clang_getTokenSpelling = Module['_clang_getTokenSpelling'] = makeInvalidEarlyAccess('_clang_getTokenSpelling');
var _clang_getTokenLocation = Module['_clang_getTokenLocation'] = makeInvalidEarlyAccess('_clang_getTokenLocation');
var _clang_getTokenExtent = Module['_clang_getTokenExtent'] = makeInvalidEarlyAccess('_clang_getTokenExtent');
var _clang_getToken = Module['_clang_getToken'] = makeInvalidEarlyAccess('_clang_getToken');
var _clang_tokenize = Module['_clang_tokenize'] = makeInvalidEarlyAccess('_clang_tokenize');
var _clang_disposeTokens = Module['_clang_disposeTokens'] = makeInvalidEarlyAccess('_clang_disposeTokens');
var _clang_annotateTokens = Module['_clang_annotateTokens'] = makeInvalidEarlyAccess('_clang_annotateTokens');
var _clang_getCursorLinkage = Module['_clang_getCursorLinkage'] = makeInvalidEarlyAccess('_clang_getCursorLinkage');
var _clang_getCursorVisibility = Module['_clang_getCursorVisibility'] = makeInvalidEarlyAccess('_clang_getCursorVisibility');
var _clang_getCursorAvailability = Module['_clang_getCursorAvailability'] = makeInvalidEarlyAccess('_clang_getCursorAvailability');
var _clang_getCursorPlatformAvailability = Module['_clang_getCursorPlatformAvailability'] = makeInvalidEarlyAccess('_clang_getCursorPlatformAvailability');
var _clang_disposeCXPlatformAvailability = Module['_clang_disposeCXPlatformAvailability'] = makeInvalidEarlyAccess('_clang_disposeCXPlatformAvailability');
var _clang_getCursorLanguage = Module['_clang_getCursorLanguage'] = makeInvalidEarlyAccess('_clang_getCursorLanguage');
var _clang_getCursorTLSKind = Module['_clang_getCursorTLSKind'] = makeInvalidEarlyAccess('_clang_getCursorTLSKind');
var _clang_Cursor_getStorageClass = Module['_clang_Cursor_getStorageClass'] = makeInvalidEarlyAccess('_clang_Cursor_getStorageClass');
var _clang_getCursorSemanticParent = Module['_clang_getCursorSemanticParent'] = makeInvalidEarlyAccess('_clang_getCursorSemanticParent');
var _clang_getCursorLexicalParent = Module['_clang_getCursorLexicalParent'] = makeInvalidEarlyAccess('_clang_getCursorLexicalParent');
var _clang_getIncludedFile = Module['_clang_getIncludedFile'] = makeInvalidEarlyAccess('_clang_getIncludedFile');
var _clang_Cursor_getObjCPropertyAttributes = Module['_clang_Cursor_getObjCPropertyAttributes'] = makeInvalidEarlyAccess('_clang_Cursor_getObjCPropertyAttributes');
var _clang_Cursor_getObjCPropertyGetterName = Module['_clang_Cursor_getObjCPropertyGetterName'] = makeInvalidEarlyAccess('_clang_Cursor_getObjCPropertyGetterName');
var _clang_Cursor_getObjCPropertySetterName = Module['_clang_Cursor_getObjCPropertySetterName'] = makeInvalidEarlyAccess('_clang_Cursor_getObjCPropertySetterName');
var _clang_Cursor_getObjCDeclQualifiers = Module['_clang_Cursor_getObjCDeclQualifiers'] = makeInvalidEarlyAccess('_clang_Cursor_getObjCDeclQualifiers');
var _clang_Cursor_isObjCOptional = Module['_clang_Cursor_isObjCOptional'] = makeInvalidEarlyAccess('_clang_Cursor_isObjCOptional');
var _clang_Cursor_isVariadic = Module['_clang_Cursor_isVariadic'] = makeInvalidEarlyAccess('_clang_Cursor_isVariadic');
var _clang_Cursor_isExternalSymbol = Module['_clang_Cursor_isExternalSymbol'] = makeInvalidEarlyAccess('_clang_Cursor_isExternalSymbol');
var _clang_Cursor_getCommentRange = Module['_clang_Cursor_getCommentRange'] = makeInvalidEarlyAccess('_clang_Cursor_getCommentRange');
var _clang_Cursor_getRawCommentText = Module['_clang_Cursor_getRawCommentText'] = makeInvalidEarlyAccess('_clang_Cursor_getRawCommentText');
var _clang_Cursor_getBriefCommentText = Module['_clang_Cursor_getBriefCommentText'] = makeInvalidEarlyAccess('_clang_Cursor_getBriefCommentText');
var _clang_Cursor_getModule = Module['_clang_Cursor_getModule'] = makeInvalidEarlyAccess('_clang_Cursor_getModule');
var _clang_getModuleForFile = Module['_clang_getModuleForFile'] = makeInvalidEarlyAccess('_clang_getModuleForFile');
var _clang_Module_getASTFile = Module['_clang_Module_getASTFile'] = makeInvalidEarlyAccess('_clang_Module_getASTFile');
var _clang_Module_getParent = Module['_clang_Module_getParent'] = makeInvalidEarlyAccess('_clang_Module_getParent');
var _clang_Module_getName = Module['_clang_Module_getName'] = makeInvalidEarlyAccess('_clang_Module_getName');
var _clang_Module_getFullName = Module['_clang_Module_getFullName'] = makeInvalidEarlyAccess('_clang_Module_getFullName');
var _clang_Module_isSystem = Module['_clang_Module_isSystem'] = makeInvalidEarlyAccess('_clang_Module_isSystem');
var _clang_Module_getNumTopLevelHeaders = Module['_clang_Module_getNumTopLevelHeaders'] = makeInvalidEarlyAccess('_clang_Module_getNumTopLevelHeaders');
var _clang_Module_getTopLevelHeader = Module['_clang_Module_getTopLevelHeader'] = makeInvalidEarlyAccess('_clang_Module_getTopLevelHeader');
var _clang_CXXConstructor_isDefaultConstructor = Module['_clang_CXXConstructor_isDefaultConstructor'] = makeInvalidEarlyAccess('_clang_CXXConstructor_isDefaultConstructor');
var _clang_CXXConstructor_isCopyConstructor = Module['_clang_CXXConstructor_isCopyConstructor'] = makeInvalidEarlyAccess('_clang_CXXConstructor_isCopyConstructor');
var _clang_CXXConstructor_isMoveConstructor = Module['_clang_CXXConstructor_isMoveConstructor'] = makeInvalidEarlyAccess('_clang_CXXConstructor_isMoveConstructor');
var _clang_CXXConstructor_isConvertingConstructor = Module['_clang_CXXConstructor_isConvertingConstructor'] = makeInvalidEarlyAccess('_clang_CXXConstructor_isConvertingConstructor');
var _clang_CXXField_isMutable = Module['_clang_CXXField_isMutable'] = makeInvalidEarlyAccess('_clang_CXXField_isMutable');
var _clang_CXXMethod_isPureVirtual = Module['_clang_CXXMethod_isPureVirtual'] = makeInvalidEarlyAccess('_clang_CXXMethod_isPureVirtual');
var _clang_CXXMethod_isConst = Module['_clang_CXXMethod_isConst'] = makeInvalidEarlyAccess('_clang_CXXMethod_isConst');
var _clang_CXXMethod_isDefaulted = Module['_clang_CXXMethod_isDefaulted'] = makeInvalidEarlyAccess('_clang_CXXMethod_isDefaulted');
var _clang_CXXMethod_isStatic = Module['_clang_CXXMethod_isStatic'] = makeInvalidEarlyAccess('_clang_CXXMethod_isStatic');
var _clang_CXXMethod_isVirtual = Module['_clang_CXXMethod_isVirtual'] = makeInvalidEarlyAccess('_clang_CXXMethod_isVirtual');
var _clang_CXXRecord_isAbstract = Module['_clang_CXXRecord_isAbstract'] = makeInvalidEarlyAccess('_clang_CXXRecord_isAbstract');
var _clang_EnumDecl_isScoped = Module['_clang_EnumDecl_isScoped'] = makeInvalidEarlyAccess('_clang_EnumDecl_isScoped');
var _clang_getIBOutletCollectionType = Module['_clang_getIBOutletCollectionType'] = makeInvalidEarlyAccess('_clang_getIBOutletCollectionType');
var _clang_getSkippedRanges = Module['_clang_getSkippedRanges'] = makeInvalidEarlyAccess('_clang_getSkippedRanges');
var _clang_getAllSkippedRanges = Module['_clang_getAllSkippedRanges'] = makeInvalidEarlyAccess('_clang_getAllSkippedRanges');
var _clang_disposeSourceRangeList = Module['_clang_disposeSourceRangeList'] = makeInvalidEarlyAccess('_clang_disposeSourceRangeList');
var _clang_Cursor_getVarDeclInitializer = Module['_clang_Cursor_getVarDeclInitializer'] = makeInvalidEarlyAccess('_clang_Cursor_getVarDeclInitializer');
var _clang_Cursor_hasVarDeclGlobalStorage = Module['_clang_Cursor_hasVarDeclGlobalStorage'] = makeInvalidEarlyAccess('_clang_Cursor_hasVarDeclGlobalStorage');
var _clang_Cursor_hasVarDeclExternalStorage = Module['_clang_Cursor_hasVarDeclExternalStorage'] = makeInvalidEarlyAccess('_clang_Cursor_hasVarDeclExternalStorage');
var _clang_getClangVersion = Module['_clang_getClangVersion'] = makeInvalidEarlyAccess('_clang_getClangVersion');
var _clang_isVirtualBase = Module['_clang_isVirtualBase'] = makeInvalidEarlyAccess('_clang_isVirtualBase');
var _clang_getCXXAccessSpecifier = Module['_clang_getCXXAccessSpecifier'] = makeInvalidEarlyAccess('_clang_getCXXAccessSpecifier');
var _clang_getTemplateCursorKind = Module['_clang_getTemplateCursorKind'] = makeInvalidEarlyAccess('_clang_getTemplateCursorKind');
var _clang_getSpecializedCursorTemplate = Module['_clang_getSpecializedCursorTemplate'] = makeInvalidEarlyAccess('_clang_getSpecializedCursorTemplate');
var _clang_getCompletionChunkKind = Module['_clang_getCompletionChunkKind'] = makeInvalidEarlyAccess('_clang_getCompletionChunkKind');
var _clang_getCompletionChunkText = Module['_clang_getCompletionChunkText'] = makeInvalidEarlyAccess('_clang_getCompletionChunkText');
var _clang_getCompletionChunkCompletionString = Module['_clang_getCompletionChunkCompletionString'] = makeInvalidEarlyAccess('_clang_getCompletionChunkCompletionString');
var _clang_getNumCompletionChunks = Module['_clang_getNumCompletionChunks'] = makeInvalidEarlyAccess('_clang_getNumCompletionChunks');
var _clang_getCompletionPriority = Module['_clang_getCompletionPriority'] = makeInvalidEarlyAccess('_clang_getCompletionPriority');
var _clang_getCompletionAvailability = Module['_clang_getCompletionAvailability'] = makeInvalidEarlyAccess('_clang_getCompletionAvailability');
var _clang_getCompletionNumAnnotations = Module['_clang_getCompletionNumAnnotations'] = makeInvalidEarlyAccess('_clang_getCompletionNumAnnotations');
var _clang_getCompletionAnnotation = Module['_clang_getCompletionAnnotation'] = makeInvalidEarlyAccess('_clang_getCompletionAnnotation');
var _clang_getCompletionParent = Module['_clang_getCompletionParent'] = makeInvalidEarlyAccess('_clang_getCompletionParent');
var _clang_getCompletionBriefComment = Module['_clang_getCompletionBriefComment'] = makeInvalidEarlyAccess('_clang_getCompletionBriefComment');
var _clang_getCompletionNumFixIts = Module['_clang_getCompletionNumFixIts'] = makeInvalidEarlyAccess('_clang_getCompletionNumFixIts');
var _clang_getCompletionFixIt = Module['_clang_getCompletionFixIt'] = makeInvalidEarlyAccess('_clang_getCompletionFixIt');
var _clang_codeCompleteAt = Module['_clang_codeCompleteAt'] = makeInvalidEarlyAccess('_clang_codeCompleteAt');
var _clang_defaultCodeCompleteOptions = Module['_clang_defaultCodeCompleteOptions'] = makeInvalidEarlyAccess('_clang_defaultCodeCompleteOptions');
var _clang_disposeCodeCompleteResults = Module['_clang_disposeCodeCompleteResults'] = makeInvalidEarlyAccess('_clang_disposeCodeCompleteResults');
var _clang_codeCompleteGetNumDiagnostics = Module['_clang_codeCompleteGetNumDiagnostics'] = makeInvalidEarlyAccess('_clang_codeCompleteGetNumDiagnostics');
var _clang_codeCompleteGetDiagnostic = Module['_clang_codeCompleteGetDiagnostic'] = makeInvalidEarlyAccess('_clang_codeCompleteGetDiagnostic');
var _clang_codeCompleteGetContexts = Module['_clang_codeCompleteGetContexts'] = makeInvalidEarlyAccess('_clang_codeCompleteGetContexts');
var _clang_codeCompleteGetContainerKind = Module['_clang_codeCompleteGetContainerKind'] = makeInvalidEarlyAccess('_clang_codeCompleteGetContainerKind');
var _clang_codeCompleteGetContainerUSR = Module['_clang_codeCompleteGetContainerUSR'] = makeInvalidEarlyAccess('_clang_codeCompleteGetContainerUSR');
var _clang_codeCompleteGetObjCSelector = Module['_clang_codeCompleteGetObjCSelector'] = makeInvalidEarlyAccess('_clang_codeCompleteGetObjCSelector');
var _clang_sortCodeCompletionResults = Module['_clang_sortCodeCompletionResults'] = makeInvalidEarlyAccess('_clang_sortCodeCompletionResults');
var _clang_getNumDiagnostics = Module['_clang_getNumDiagnostics'] = makeInvalidEarlyAccess('_clang_getNumDiagnostics');
var _clang_getDiagnostic = Module['_clang_getDiagnostic'] = makeInvalidEarlyAccess('_clang_getDiagnostic');
var _clang_getDiagnosticSetFromTU = Module['_clang_getDiagnosticSetFromTU'] = makeInvalidEarlyAccess('_clang_getDiagnosticSetFromTU');
var _clang_disposeDiagnostic = Module['_clang_disposeDiagnostic'] = makeInvalidEarlyAccess('_clang_disposeDiagnostic');
var _clang_formatDiagnostic = Module['_clang_formatDiagnostic'] = makeInvalidEarlyAccess('_clang_formatDiagnostic');
var _clang_getDiagnosticRange = Module['_clang_getDiagnosticRange'] = makeInvalidEarlyAccess('_clang_getDiagnosticRange');
var _clang_getDiagnosticSeverity = Module['_clang_getDiagnosticSeverity'] = makeInvalidEarlyAccess('_clang_getDiagnosticSeverity');
var _clang_getDiagnosticLocation = Module['_clang_getDiagnosticLocation'] = makeInvalidEarlyAccess('_clang_getDiagnosticLocation');
var _clang_getDiagnosticNumRanges = Module['_clang_getDiagnosticNumRanges'] = makeInvalidEarlyAccess('_clang_getDiagnosticNumRanges');
var _clang_getDiagnosticSpelling = Module['_clang_getDiagnosticSpelling'] = makeInvalidEarlyAccess('_clang_getDiagnosticSpelling');
var _clang_getDiagnosticOption = Module['_clang_getDiagnosticOption'] = makeInvalidEarlyAccess('_clang_getDiagnosticOption');
var _clang_getDiagnosticCategory = Module['_clang_getDiagnosticCategory'] = makeInvalidEarlyAccess('_clang_getDiagnosticCategory');
var _clang_getDiagnosticCategoryText = Module['_clang_getDiagnosticCategoryText'] = makeInvalidEarlyAccess('_clang_getDiagnosticCategoryText');
var _clang_defaultDiagnosticDisplayOptions = Module['_clang_defaultDiagnosticDisplayOptions'] = makeInvalidEarlyAccess('_clang_defaultDiagnosticDisplayOptions');
var _clang_getDiagnosticCategoryName = Module['_clang_getDiagnosticCategoryName'] = makeInvalidEarlyAccess('_clang_getDiagnosticCategoryName');
var _clang_getDiagnosticNumFixIts = Module['_clang_getDiagnosticNumFixIts'] = makeInvalidEarlyAccess('_clang_getDiagnosticNumFixIts');
var _clang_getDiagnosticFixIt = Module['_clang_getDiagnosticFixIt'] = makeInvalidEarlyAccess('_clang_getDiagnosticFixIt');
var _clang_disposeDiagnosticSet = Module['_clang_disposeDiagnosticSet'] = makeInvalidEarlyAccess('_clang_disposeDiagnosticSet');
var _clang_getDiagnosticInSet = Module['_clang_getDiagnosticInSet'] = makeInvalidEarlyAccess('_clang_getDiagnosticInSet');
var _clang_getChildDiagnostics = Module['_clang_getChildDiagnostics'] = makeInvalidEarlyAccess('_clang_getChildDiagnostics');
var _clang_getNumDiagnosticsInSet = Module['_clang_getNumDiagnosticsInSet'] = makeInvalidEarlyAccess('_clang_getNumDiagnosticsInSet');
var _clang_findReferencesInFile = Module['_clang_findReferencesInFile'] = makeInvalidEarlyAccess('_clang_findReferencesInFile');
var _clang_findIncludesInFile = Module['_clang_findIncludesInFile'] = makeInvalidEarlyAccess('_clang_findIncludesInFile');
var _clang_findReferencesInFileWithBlock = Module['_clang_findReferencesInFileWithBlock'] = makeInvalidEarlyAccess('_clang_findReferencesInFileWithBlock');
var _clang_findIncludesInFileWithBlock = Module['_clang_findIncludesInFileWithBlock'] = makeInvalidEarlyAccess('_clang_findIncludesInFileWithBlock');
var _clang_getInclusions = Module['_clang_getInclusions'] = makeInvalidEarlyAccess('_clang_getInclusions');
var _clang_getCursorUSR = Module['_clang_getCursorUSR'] = makeInvalidEarlyAccess('_clang_getCursorUSR');
var _clang_constructUSR_ObjCIvar = Module['_clang_constructUSR_ObjCIvar'] = makeInvalidEarlyAccess('_clang_constructUSR_ObjCIvar');
var _clang_constructUSR_ObjCMethod = Module['_clang_constructUSR_ObjCMethod'] = makeInvalidEarlyAccess('_clang_constructUSR_ObjCMethod');
var _clang_constructUSR_ObjCClass = Module['_clang_constructUSR_ObjCClass'] = makeInvalidEarlyAccess('_clang_constructUSR_ObjCClass');
var _clang_constructUSR_ObjCProtocol = Module['_clang_constructUSR_ObjCProtocol'] = makeInvalidEarlyAccess('_clang_constructUSR_ObjCProtocol');
var _clang_constructUSR_ObjCCategory = Module['_clang_constructUSR_ObjCCategory'] = makeInvalidEarlyAccess('_clang_constructUSR_ObjCCategory');
var _clang_constructUSR_ObjCProperty = Module['_clang_constructUSR_ObjCProperty'] = makeInvalidEarlyAccess('_clang_constructUSR_ObjCProperty');
var _clang_Cursor_getParsedComment = Module['_clang_Cursor_getParsedComment'] = makeInvalidEarlyAccess('_clang_Cursor_getParsedComment');
var _clang_Comment_getKind = Module['_clang_Comment_getKind'] = makeInvalidEarlyAccess('_clang_Comment_getKind');
var _clang_Comment_getNumChildren = Module['_clang_Comment_getNumChildren'] = makeInvalidEarlyAccess('_clang_Comment_getNumChildren');
var _clang_Comment_getChild = Module['_clang_Comment_getChild'] = makeInvalidEarlyAccess('_clang_Comment_getChild');
var _clang_Comment_isWhitespace = Module['_clang_Comment_isWhitespace'] = makeInvalidEarlyAccess('_clang_Comment_isWhitespace');
var _clang_InlineContentComment_hasTrailingNewline = Module['_clang_InlineContentComment_hasTrailingNewline'] = makeInvalidEarlyAccess('_clang_InlineContentComment_hasTrailingNewline');
var _clang_TextComment_getText = Module['_clang_TextComment_getText'] = makeInvalidEarlyAccess('_clang_TextComment_getText');
var _clang_InlineCommandComment_getCommandName = Module['_clang_InlineCommandComment_getCommandName'] = makeInvalidEarlyAccess('_clang_InlineCommandComment_getCommandName');
var _clang_InlineCommandComment_getRenderKind = Module['_clang_InlineCommandComment_getRenderKind'] = makeInvalidEarlyAccess('_clang_InlineCommandComment_getRenderKind');
var _clang_InlineCommandComment_getNumArgs = Module['_clang_InlineCommandComment_getNumArgs'] = makeInvalidEarlyAccess('_clang_InlineCommandComment_getNumArgs');
var _clang_InlineCommandComment_getArgText = Module['_clang_InlineCommandComment_getArgText'] = makeInvalidEarlyAccess('_clang_InlineCommandComment_getArgText');
var _clang_HTMLTagComment_getTagName = Module['_clang_HTMLTagComment_getTagName'] = makeInvalidEarlyAccess('_clang_HTMLTagComment_getTagName');
var _clang_HTMLStartTagComment_isSelfClosing = Module['_clang_HTMLStartTagComment_isSelfClosing'] = makeInvalidEarlyAccess('_clang_HTMLStartTagComment_isSelfClosing');
var _clang_HTMLStartTag_getNumAttrs = Module['_clang_HTMLStartTag_getNumAttrs'] = makeInvalidEarlyAccess('_clang_HTMLStartTag_getNumAttrs');
var _clang_HTMLStartTag_getAttrName = Module['_clang_HTMLStartTag_getAttrName'] = makeInvalidEarlyAccess('_clang_HTMLStartTag_getAttrName');
var _clang_HTMLStartTag_getAttrValue = Module['_clang_HTMLStartTag_getAttrValue'] = makeInvalidEarlyAccess('_clang_HTMLStartTag_getAttrValue');
var _clang_BlockCommandComment_getCommandName = Module['_clang_BlockCommandComment_getCommandName'] = makeInvalidEarlyAccess('_clang_BlockCommandComment_getCommandName');
var _clang_BlockCommandComment_getNumArgs = Module['_clang_BlockCommandComment_getNumArgs'] = makeInvalidEarlyAccess('_clang_BlockCommandComment_getNumArgs');
var _clang_BlockCommandComment_getArgText = Module['_clang_BlockCommandComment_getArgText'] = makeInvalidEarlyAccess('_clang_BlockCommandComment_getArgText');
var _clang_BlockCommandComment_getParagraph = Module['_clang_BlockCommandComment_getParagraph'] = makeInvalidEarlyAccess('_clang_BlockCommandComment_getParagraph');
var _clang_ParamCommandComment_getParamName = Module['_clang_ParamCommandComment_getParamName'] = makeInvalidEarlyAccess('_clang_ParamCommandComment_getParamName');
var _clang_ParamCommandComment_isParamIndexValid = Module['_clang_ParamCommandComment_isParamIndexValid'] = makeInvalidEarlyAccess('_clang_ParamCommandComment_isParamIndexValid');
var _clang_ParamCommandComment_getParamIndex = Module['_clang_ParamCommandComment_getParamIndex'] = makeInvalidEarlyAccess('_clang_ParamCommandComment_getParamIndex');
var _clang_ParamCommandComment_isDirectionExplicit = Module['_clang_ParamCommandComment_isDirectionExplicit'] = makeInvalidEarlyAccess('_clang_ParamCommandComment_isDirectionExplicit');
var _clang_ParamCommandComment_getDirection = Module['_clang_ParamCommandComment_getDirection'] = makeInvalidEarlyAccess('_clang_ParamCommandComment_getDirection');
var _clang_TParamCommandComment_getParamName = Module['_clang_TParamCommandComment_getParamName'] = makeInvalidEarlyAccess('_clang_TParamCommandComment_getParamName');
var _clang_TParamCommandComment_isParamPositionValid = Module['_clang_TParamCommandComment_isParamPositionValid'] = makeInvalidEarlyAccess('_clang_TParamCommandComment_isParamPositionValid');
var _clang_TParamCommandComment_getDepth = Module['_clang_TParamCommandComment_getDepth'] = makeInvalidEarlyAccess('_clang_TParamCommandComment_getDepth');
var _clang_TParamCommandComment_getIndex = Module['_clang_TParamCommandComment_getIndex'] = makeInvalidEarlyAccess('_clang_TParamCommandComment_getIndex');
var _clang_VerbatimBlockLineComment_getText = Module['_clang_VerbatimBlockLineComment_getText'] = makeInvalidEarlyAccess('_clang_VerbatimBlockLineComment_getText');
var _clang_VerbatimLineComment_getText = Module['_clang_VerbatimLineComment_getText'] = makeInvalidEarlyAccess('_clang_VerbatimLineComment_getText');
var _clang_HTMLTagComment_getAsString = Module['_clang_HTMLTagComment_getAsString'] = makeInvalidEarlyAccess('_clang_HTMLTagComment_getAsString');
var _clang_FullComment_getAsHTML = Module['_clang_FullComment_getAsHTML'] = makeInvalidEarlyAccess('_clang_FullComment_getAsHTML');
var _clang_FullComment_getAsXML = Module['_clang_FullComment_getAsXML'] = makeInvalidEarlyAccess('_clang_FullComment_getAsXML');
var _clang_Cursor_isNull = Module['_clang_Cursor_isNull'] = makeInvalidEarlyAccess('_clang_Cursor_isNull');
var _clang_Cursor_getTranslationUnit = Module['_clang_Cursor_getTranslationUnit'] = makeInvalidEarlyAccess('_clang_Cursor_getTranslationUnit');
var _clang_Cursor_getNumArguments = Module['_clang_Cursor_getNumArguments'] = makeInvalidEarlyAccess('_clang_Cursor_getNumArguments');
var _clang_Cursor_getArgument = Module['_clang_Cursor_getArgument'] = makeInvalidEarlyAccess('_clang_Cursor_getArgument');
var _clang_Cursor_getNumTemplateArguments = Module['_clang_Cursor_getNumTemplateArguments'] = makeInvalidEarlyAccess('_clang_Cursor_getNumTemplateArguments');
var _clang_Cursor_getTemplateArgumentKind = Module['_clang_Cursor_getTemplateArgumentKind'] = makeInvalidEarlyAccess('_clang_Cursor_getTemplateArgumentKind');
var _clang_Cursor_getTemplateArgumentType = Module['_clang_Cursor_getTemplateArgumentType'] = makeInvalidEarlyAccess('_clang_Cursor_getTemplateArgumentType');
var _clang_Cursor_getTemplateArgumentValue = Module['_clang_Cursor_getTemplateArgumentValue'] = makeInvalidEarlyAccess('_clang_Cursor_getTemplateArgumentValue');
var _clang_Cursor_getTemplateArgumentUnsignedValue = Module['_clang_Cursor_getTemplateArgumentUnsignedValue'] = makeInvalidEarlyAccess('_clang_Cursor_getTemplateArgumentUnsignedValue');
var _clang_createCXCursorSet = Module['_clang_createCXCursorSet'] = makeInvalidEarlyAccess('_clang_createCXCursorSet');
var _clang_disposeCXCursorSet = Module['_clang_disposeCXCursorSet'] = makeInvalidEarlyAccess('_clang_disposeCXCursorSet');
var _clang_CXCursorSet_contains = Module['_clang_CXCursorSet_contains'] = makeInvalidEarlyAccess('_clang_CXCursorSet_contains');
var _clang_CXCursorSet_insert = Module['_clang_CXCursorSet_insert'] = makeInvalidEarlyAccess('_clang_CXCursorSet_insert');
var _clang_getCursorCompletionString = Module['_clang_getCursorCompletionString'] = makeInvalidEarlyAccess('_clang_getCursorCompletionString');
var _clang_getOverriddenCursors = Module['_clang_getOverriddenCursors'] = makeInvalidEarlyAccess('_clang_getOverriddenCursors');
var _clang_disposeOverriddenCursors = Module['_clang_disposeOverriddenCursors'] = makeInvalidEarlyAccess('_clang_disposeOverriddenCursors');
var _clang_Cursor_isDynamicCall = Module['_clang_Cursor_isDynamicCall'] = makeInvalidEarlyAccess('_clang_Cursor_isDynamicCall');
var _clang_Cursor_getReceiverType = Module['_clang_Cursor_getReceiverType'] = makeInvalidEarlyAccess('_clang_Cursor_getReceiverType');
var _clang_CompilationDatabase_fromDirectory = Module['_clang_CompilationDatabase_fromDirectory'] = makeInvalidEarlyAccess('_clang_CompilationDatabase_fromDirectory');
var _clang_CompilationDatabase_dispose = Module['_clang_CompilationDatabase_dispose'] = makeInvalidEarlyAccess('_clang_CompilationDatabase_dispose');
var _clang_CompilationDatabase_getCompileCommands = Module['_clang_CompilationDatabase_getCompileCommands'] = makeInvalidEarlyAccess('_clang_CompilationDatabase_getCompileCommands');
var _clang_CompilationDatabase_getAllCompileCommands = Module['_clang_CompilationDatabase_getAllCompileCommands'] = makeInvalidEarlyAccess('_clang_CompilationDatabase_getAllCompileCommands');
var _clang_CompileCommands_dispose = Module['_clang_CompileCommands_dispose'] = makeInvalidEarlyAccess('_clang_CompileCommands_dispose');
var _clang_CompileCommands_getSize = Module['_clang_CompileCommands_getSize'] = makeInvalidEarlyAccess('_clang_CompileCommands_getSize');
var _clang_CompileCommands_getCommand = Module['_clang_CompileCommands_getCommand'] = makeInvalidEarlyAccess('_clang_CompileCommands_getCommand');
var _clang_CompileCommand_getDirectory = Module['_clang_CompileCommand_getDirectory'] = makeInvalidEarlyAccess('_clang_CompileCommand_getDirectory');
var _clang_CompileCommand_getFilename = Module['_clang_CompileCommand_getFilename'] = makeInvalidEarlyAccess('_clang_CompileCommand_getFilename');
var _clang_CompileCommand_getNumArgs = Module['_clang_CompileCommand_getNumArgs'] = makeInvalidEarlyAccess('_clang_CompileCommand_getNumArgs');
var _clang_CompileCommand_getArg = Module['_clang_CompileCommand_getArg'] = makeInvalidEarlyAccess('_clang_CompileCommand_getArg');
var _clang_CompileCommand_getNumMappedSources = Module['_clang_CompileCommand_getNumMappedSources'] = makeInvalidEarlyAccess('_clang_CompileCommand_getNumMappedSources');
var _clang_CompileCommand_getMappedSourcePath = Module['_clang_CompileCommand_getMappedSourcePath'] = makeInvalidEarlyAccess('_clang_CompileCommand_getMappedSourcePath');
var _clang_CompileCommand_getMappedSourceContent = Module['_clang_CompileCommand_getMappedSourceContent'] = makeInvalidEarlyAccess('_clang_CompileCommand_getMappedSourceContent');
var _clang_loadDiagnostics = Module['_clang_loadDiagnostics'] = makeInvalidEarlyAccess('_clang_loadDiagnostics');
var _clang_getNullLocation = Module['_clang_getNullLocation'] = makeInvalidEarlyAccess('_clang_getNullLocation');
var _clang_equalLocations = Module['_clang_equalLocations'] = makeInvalidEarlyAccess('_clang_equalLocations');
var _clang_getNullRange = Module['_clang_getNullRange'] = makeInvalidEarlyAccess('_clang_getNullRange');
var _clang_getRange = Module['_clang_getRange'] = makeInvalidEarlyAccess('_clang_getRange');
var _clang_equalRanges = Module['_clang_equalRanges'] = makeInvalidEarlyAccess('_clang_equalRanges');
var _clang_Range_isNull = Module['_clang_Range_isNull'] = makeInvalidEarlyAccess('_clang_Range_isNull');
var _clang_getRangeStart = Module['_clang_getRangeStart'] = makeInvalidEarlyAccess('_clang_getRangeStart');
var _clang_getRangeEnd = Module['_clang_getRangeEnd'] = makeInvalidEarlyAccess('_clang_getRangeEnd');
var _clang_getLocation = Module['_clang_getLocation'] = makeInvalidEarlyAccess('_clang_getLocation');
var _clang_getLocationForOffset = Module['_clang_getLocationForOffset'] = makeInvalidEarlyAccess('_clang_getLocationForOffset');
var _clang_Location_isInSystemHeader = Module['_clang_Location_isInSystemHeader'] = makeInvalidEarlyAccess('_clang_Location_isInSystemHeader');
var _clang_Location_isFromMainFile = Module['_clang_Location_isFromMainFile'] = makeInvalidEarlyAccess('_clang_Location_isFromMainFile');
var _clang_getExpansionLocation = Module['_clang_getExpansionLocation'] = makeInvalidEarlyAccess('_clang_getExpansionLocation');
var _clang_getPresumedLocation = Module['_clang_getPresumedLocation'] = makeInvalidEarlyAccess('_clang_getPresumedLocation');
var _clang_getInstantiationLocation = Module['_clang_getInstantiationLocation'] = makeInvalidEarlyAccess('_clang_getInstantiationLocation');
var _clang_getSpellingLocation = Module['_clang_getSpellingLocation'] = makeInvalidEarlyAccess('_clang_getSpellingLocation');
var _clang_getFileLocation = Module['_clang_getFileLocation'] = makeInvalidEarlyAccess('_clang_getFileLocation');
var _clang_getCString = Module['_clang_getCString'] = makeInvalidEarlyAccess('_clang_getCString');
var _clang_disposeString = Module['_clang_disposeString'] = makeInvalidEarlyAccess('_clang_disposeString');
var _clang_disposeStringSet = Module['_clang_disposeStringSet'] = makeInvalidEarlyAccess('_clang_disposeStringSet');
var _clang_getCursorType = Module['_clang_getCursorType'] = makeInvalidEarlyAccess('_clang_getCursorType');
var _clang_getTypeSpelling = Module['_clang_getTypeSpelling'] = makeInvalidEarlyAccess('_clang_getTypeSpelling');
var _clang_getTypedefDeclUnderlyingType = Module['_clang_getTypedefDeclUnderlyingType'] = makeInvalidEarlyAccess('_clang_getTypedefDeclUnderlyingType');
var _clang_getEnumDeclIntegerType = Module['_clang_getEnumDeclIntegerType'] = makeInvalidEarlyAccess('_clang_getEnumDeclIntegerType');
var _clang_getEnumConstantDeclValue = Module['_clang_getEnumConstantDeclValue'] = makeInvalidEarlyAccess('_clang_getEnumConstantDeclValue');
var _clang_getEnumConstantDeclUnsignedValue = Module['_clang_getEnumConstantDeclUnsignedValue'] = makeInvalidEarlyAccess('_clang_getEnumConstantDeclUnsignedValue');
var _clang_getFieldDeclBitWidth = Module['_clang_getFieldDeclBitWidth'] = makeInvalidEarlyAccess('_clang_getFieldDeclBitWidth');
var _clang_getCanonicalType = Module['_clang_getCanonicalType'] = makeInvalidEarlyAccess('_clang_getCanonicalType');
var _clang_isConstQualifiedType = Module['_clang_isConstQualifiedType'] = makeInvalidEarlyAccess('_clang_isConstQualifiedType');
var _clang_isVolatileQualifiedType = Module['_clang_isVolatileQualifiedType'] = makeInvalidEarlyAccess('_clang_isVolatileQualifiedType');
var _clang_isRestrictQualifiedType = Module['_clang_isRestrictQualifiedType'] = makeInvalidEarlyAccess('_clang_isRestrictQualifiedType');
var _clang_getAddressSpace = Module['_clang_getAddressSpace'] = makeInvalidEarlyAccess('_clang_getAddressSpace');
var _clang_getTypedefName = Module['_clang_getTypedefName'] = makeInvalidEarlyAccess('_clang_getTypedefName');
var _clang_getPointeeType = Module['_clang_getPointeeType'] = makeInvalidEarlyAccess('_clang_getPointeeType');
var _clang_getTypeDeclaration = Module['_clang_getTypeDeclaration'] = makeInvalidEarlyAccess('_clang_getTypeDeclaration');
var _clang_getTypeKindSpelling = Module['_clang_getTypeKindSpelling'] = makeInvalidEarlyAccess('_clang_getTypeKindSpelling');
var _clang_equalTypes = Module['_clang_equalTypes'] = makeInvalidEarlyAccess('_clang_equalTypes');
var _clang_isFunctionTypeVariadic = Module['_clang_isFunctionTypeVariadic'] = makeInvalidEarlyAccess('_clang_isFunctionTypeVariadic');
var _clang_getFunctionTypeCallingConv = Module['_clang_getFunctionTypeCallingConv'] = makeInvalidEarlyAccess('_clang_getFunctionTypeCallingConv');
var _clang_getNumArgTypes = Module['_clang_getNumArgTypes'] = makeInvalidEarlyAccess('_clang_getNumArgTypes');
var _clang_getArgType = Module['_clang_getArgType'] = makeInvalidEarlyAccess('_clang_getArgType');
var _clang_getResultType = Module['_clang_getResultType'] = makeInvalidEarlyAccess('_clang_getResultType');
var _clang_getCursorResultType = Module['_clang_getCursorResultType'] = makeInvalidEarlyAccess('_clang_getCursorResultType');
var _clang_getExceptionSpecificationType = Module['_clang_getExceptionSpecificationType'] = makeInvalidEarlyAccess('_clang_getExceptionSpecificationType');
var _clang_getCursorExceptionSpecificationType = Module['_clang_getCursorExceptionSpecificationType'] = makeInvalidEarlyAccess('_clang_getCursorExceptionSpecificationType');
var _clang_isPODType = Module['_clang_isPODType'] = makeInvalidEarlyAccess('_clang_isPODType');
var _clang_getElementType = Module['_clang_getElementType'] = makeInvalidEarlyAccess('_clang_getElementType');
var _clang_getNumElements = Module['_clang_getNumElements'] = makeInvalidEarlyAccess('_clang_getNumElements');
var _clang_getArrayElementType = Module['_clang_getArrayElementType'] = makeInvalidEarlyAccess('_clang_getArrayElementType');
var _clang_getArraySize = Module['_clang_getArraySize'] = makeInvalidEarlyAccess('_clang_getArraySize');
var _clang_Type_getAlignOf = Module['_clang_Type_getAlignOf'] = makeInvalidEarlyAccess('_clang_Type_getAlignOf');
var _clang_Type_getClassType = Module['_clang_Type_getClassType'] = makeInvalidEarlyAccess('_clang_Type_getClassType');
var _clang_Type_getSizeOf = Module['_clang_Type_getSizeOf'] = makeInvalidEarlyAccess('_clang_Type_getSizeOf');
var _clang_Type_getOffsetOf = Module['_clang_Type_getOffsetOf'] = makeInvalidEarlyAccess('_clang_Type_getOffsetOf');
var _clang_Type_getModifiedType = Module['_clang_Type_getModifiedType'] = makeInvalidEarlyAccess('_clang_Type_getModifiedType');
var _clang_Cursor_getOffsetOfField = Module['_clang_Cursor_getOffsetOfField'] = makeInvalidEarlyAccess('_clang_Cursor_getOffsetOfField');
var _clang_Type_getCXXRefQualifier = Module['_clang_Type_getCXXRefQualifier'] = makeInvalidEarlyAccess('_clang_Type_getCXXRefQualifier');
var _clang_Cursor_isBitField = Module['_clang_Cursor_isBitField'] = makeInvalidEarlyAccess('_clang_Cursor_isBitField');
var _clang_getDeclObjCTypeEncoding = Module['_clang_getDeclObjCTypeEncoding'] = makeInvalidEarlyAccess('_clang_getDeclObjCTypeEncoding');
var _clang_Type_getNumTemplateArguments = Module['_clang_Type_getNumTemplateArguments'] = makeInvalidEarlyAccess('_clang_Type_getNumTemplateArguments');
var _clang_Type_getTemplateArgumentAsType = Module['_clang_Type_getTemplateArgumentAsType'] = makeInvalidEarlyAccess('_clang_Type_getTemplateArgumentAsType');
var _clang_Type_getObjCObjectBaseType = Module['_clang_Type_getObjCObjectBaseType'] = makeInvalidEarlyAccess('_clang_Type_getObjCObjectBaseType');
var _clang_Type_getNumObjCProtocolRefs = Module['_clang_Type_getNumObjCProtocolRefs'] = makeInvalidEarlyAccess('_clang_Type_getNumObjCProtocolRefs');
var _clang_Type_getObjCProtocolDecl = Module['_clang_Type_getObjCProtocolDecl'] = makeInvalidEarlyAccess('_clang_Type_getObjCProtocolDecl');
var _clang_Type_getNumObjCTypeArgs = Module['_clang_Type_getNumObjCTypeArgs'] = makeInvalidEarlyAccess('_clang_Type_getNumObjCTypeArgs');
var _clang_Type_getObjCTypeArg = Module['_clang_Type_getObjCTypeArg'] = makeInvalidEarlyAccess('_clang_Type_getObjCTypeArg');
var _clang_Type_visitFields = Module['_clang_Type_visitFields'] = makeInvalidEarlyAccess('_clang_Type_visitFields');
var _clang_Cursor_isAnonymous = Module['_clang_Cursor_isAnonymous'] = makeInvalidEarlyAccess('_clang_Cursor_isAnonymous');
var _clang_Cursor_isAnonymousRecordDecl = Module['_clang_Cursor_isAnonymousRecordDecl'] = makeInvalidEarlyAccess('_clang_Cursor_isAnonymousRecordDecl');
var _clang_Cursor_isInlineNamespace = Module['_clang_Cursor_isInlineNamespace'] = makeInvalidEarlyAccess('_clang_Cursor_isInlineNamespace');
var _clang_Type_getNamedType = Module['_clang_Type_getNamedType'] = makeInvalidEarlyAccess('_clang_Type_getNamedType');
var _clang_Type_isTransparentTagTypedef = Module['_clang_Type_isTransparentTagTypedef'] = makeInvalidEarlyAccess('_clang_Type_isTransparentTagTypedef');
var _clang_Type_getNullability = Module['_clang_Type_getNullability'] = makeInvalidEarlyAccess('_clang_Type_getNullability');
var _clang_Type_getValueType = Module['_clang_Type_getValueType'] = makeInvalidEarlyAccess('_clang_Type_getValueType');
var _clang_index_isEntityObjCContainerKind = Module['_clang_index_isEntityObjCContainerKind'] = makeInvalidEarlyAccess('_clang_index_isEntityObjCContainerKind');
var _clang_index_getObjCContainerDeclInfo = Module['_clang_index_getObjCContainerDeclInfo'] = makeInvalidEarlyAccess('_clang_index_getObjCContainerDeclInfo');
var _clang_index_getObjCInterfaceDeclInfo = Module['_clang_index_getObjCInterfaceDeclInfo'] = makeInvalidEarlyAccess('_clang_index_getObjCInterfaceDeclInfo');
var _clang_index_getObjCCategoryDeclInfo = Module['_clang_index_getObjCCategoryDeclInfo'] = makeInvalidEarlyAccess('_clang_index_getObjCCategoryDeclInfo');
var _clang_index_getObjCProtocolRefListInfo = Module['_clang_index_getObjCProtocolRefListInfo'] = makeInvalidEarlyAccess('_clang_index_getObjCProtocolRefListInfo');
var _clang_index_getObjCPropertyDeclInfo = Module['_clang_index_getObjCPropertyDeclInfo'] = makeInvalidEarlyAccess('_clang_index_getObjCPropertyDeclInfo');
var _clang_index_getIBOutletCollectionAttrInfo = Module['_clang_index_getIBOutletCollectionAttrInfo'] = makeInvalidEarlyAccess('_clang_index_getIBOutletCollectionAttrInfo');
var _clang_index_getCXXClassDeclInfo = Module['_clang_index_getCXXClassDeclInfo'] = makeInvalidEarlyAccess('_clang_index_getCXXClassDeclInfo');
var _clang_index_getClientContainer = Module['_clang_index_getClientContainer'] = makeInvalidEarlyAccess('_clang_index_getClientContainer');
var _clang_index_setClientContainer = Module['_clang_index_setClientContainer'] = makeInvalidEarlyAccess('_clang_index_setClientContainer');
var _clang_index_getClientEntity = Module['_clang_index_getClientEntity'] = makeInvalidEarlyAccess('_clang_index_getClientEntity');
var _clang_index_setClientEntity = Module['_clang_index_setClientEntity'] = makeInvalidEarlyAccess('_clang_index_setClientEntity');
var _clang_IndexAction_create = Module['_clang_IndexAction_create'] = makeInvalidEarlyAccess('_clang_IndexAction_create');
var _clang_IndexAction_dispose = Module['_clang_IndexAction_dispose'] = makeInvalidEarlyAccess('_clang_IndexAction_dispose');
var _clang_indexSourceFile = Module['_clang_indexSourceFile'] = makeInvalidEarlyAccess('_clang_indexSourceFile');
var _clang_indexSourceFileFullArgv = Module['_clang_indexSourceFileFullArgv'] = makeInvalidEarlyAccess('_clang_indexSourceFileFullArgv');
var _clang_indexTranslationUnit = Module['_clang_indexTranslationUnit'] = makeInvalidEarlyAccess('_clang_indexTranslationUnit');
var _clang_indexLoc_getFileLocation = Module['_clang_indexLoc_getFileLocation'] = makeInvalidEarlyAccess('_clang_indexLoc_getFileLocation');
var _clang_indexLoc_getCXSourceLocation = Module['_clang_indexLoc_getCXSourceLocation'] = makeInvalidEarlyAccess('_clang_indexLoc_getCXSourceLocation');
var _clang_install_aborting_llvm_fatal_error_handler = Module['_clang_install_aborting_llvm_fatal_error_handler'] = makeInvalidEarlyAccess('_clang_install_aborting_llvm_fatal_error_handler');
var _clang_uninstall_llvm_fatal_error_handler = Module['_clang_uninstall_llvm_fatal_error_handler'] = makeInvalidEarlyAccess('_clang_uninstall_llvm_fatal_error_handler');
var _clang_CXRewriter_create = Module['_clang_CXRewriter_create'] = makeInvalidEarlyAccess('_clang_CXRewriter_create');
var _clang_CXRewriter_insertTextBefore = Module['_clang_CXRewriter_insertTextBefore'] = makeInvalidEarlyAccess('_clang_CXRewriter_insertTextBefore');
var _clang_CXRewriter_replaceText = Module['_clang_CXRewriter_replaceText'] = makeInvalidEarlyAccess('_clang_CXRewriter_replaceText');
var _clang_CXRewriter_removeText = Module['_clang_CXRewriter_removeText'] = makeInvalidEarlyAccess('_clang_CXRewriter_removeText');
var _clang_CXRewriter_overwriteChangedFiles = Module['_clang_CXRewriter_overwriteChangedFiles'] = makeInvalidEarlyAccess('_clang_CXRewriter_overwriteChangedFiles');
var _clang_CXRewriter_writeMainFileToStdOut = Module['_clang_CXRewriter_writeMainFileToStdOut'] = makeInvalidEarlyAccess('_clang_CXRewriter_writeMainFileToStdOut');
var _clang_CXRewriter_dispose = Module['_clang_CXRewriter_dispose'] = makeInvalidEarlyAccess('_clang_CXRewriter_dispose');
var _fflush = makeInvalidEarlyAccess('_fflush');
var __emscripten_timeout = makeInvalidEarlyAccess('__emscripten_timeout');
var _strerror = makeInvalidEarlyAccess('_strerror');
var _emscripten_builtin_memalign = makeInvalidEarlyAccess('_emscripten_builtin_memalign');
var _malloc = Module['_malloc'] = makeInvalidEarlyAccess('_malloc');
var _free = Module['_free'] = makeInvalidEarlyAccess('_free');
var _setThrew = makeInvalidEarlyAccess('_setThrew');
var _emscripten_stack_init = makeInvalidEarlyAccess('_emscripten_stack_init');
var _emscripten_stack_get_free = makeInvalidEarlyAccess('_emscripten_stack_get_free');
var _emscripten_stack_get_base = makeInvalidEarlyAccess('_emscripten_stack_get_base');
var _emscripten_stack_get_end = makeInvalidEarlyAccess('_emscripten_stack_get_end');
var __emscripten_stack_restore = makeInvalidEarlyAccess('__emscripten_stack_restore');
var __emscripten_stack_alloc = makeInvalidEarlyAccess('__emscripten_stack_alloc');
var _emscripten_stack_get_current = makeInvalidEarlyAccess('_emscripten_stack_get_current');
var memory = makeInvalidEarlyAccess('memory');
var __indirect_function_table = makeInvalidEarlyAccess('__indirect_function_table');
var wasmMemory = makeInvalidEarlyAccess('wasmMemory');
var wasmTable = makeInvalidEarlyAccess('wasmTable');

function assignWasmExports(wasmExports) {
  assert(typeof wasmExports['clang_getRemappings'] != 'undefined', 'missing Wasm export: clang_getRemappings');
  assert(typeof wasmExports['clang_getRemappingsFromFileList'] != 'undefined', 'missing Wasm export: clang_getRemappingsFromFileList');
  assert(typeof wasmExports['clang_remap_getNumFiles'] != 'undefined', 'missing Wasm export: clang_remap_getNumFiles');
  assert(typeof wasmExports['clang_remap_getFilenames'] != 'undefined', 'missing Wasm export: clang_remap_getFilenames');
  assert(typeof wasmExports['clang_remap_dispose'] != 'undefined', 'missing Wasm export: clang_remap_dispose');
  assert(typeof wasmExports['clang_getBuildSessionTimestamp'] != 'undefined', 'missing Wasm export: clang_getBuildSessionTimestamp');
  assert(typeof wasmExports['clang_VirtualFileOverlay_create'] != 'undefined', 'missing Wasm export: clang_VirtualFileOverlay_create');
  assert(typeof wasmExports['clang_VirtualFileOverlay_addFileMapping'] != 'undefined', 'missing Wasm export: clang_VirtualFileOverlay_addFileMapping');
  assert(typeof wasmExports['clang_VirtualFileOverlay_setCaseSensitivity'] != 'undefined', 'missing Wasm export: clang_VirtualFileOverlay_setCaseSensitivity');
  assert(typeof wasmExports['clang_VirtualFileOverlay_writeToBuffer'] != 'undefined', 'missing Wasm export: clang_VirtualFileOverlay_writeToBuffer');
  assert(typeof wasmExports['clang_free'] != 'undefined', 'missing Wasm export: clang_free');
  assert(typeof wasmExports['clang_VirtualFileOverlay_dispose'] != 'undefined', 'missing Wasm export: clang_VirtualFileOverlay_dispose');
  assert(typeof wasmExports['clang_ModuleMapDescriptor_create'] != 'undefined', 'missing Wasm export: clang_ModuleMapDescriptor_create');
  assert(typeof wasmExports['clang_ModuleMapDescriptor_setFrameworkModuleName'] != 'undefined', 'missing Wasm export: clang_ModuleMapDescriptor_setFrameworkModuleName');
  assert(typeof wasmExports['clang_ModuleMapDescriptor_setUmbrellaHeader'] != 'undefined', 'missing Wasm export: clang_ModuleMapDescriptor_setUmbrellaHeader');
  assert(typeof wasmExports['clang_ModuleMapDescriptor_writeToBuffer'] != 'undefined', 'missing Wasm export: clang_ModuleMapDescriptor_writeToBuffer');
  assert(typeof wasmExports['clang_ModuleMapDescriptor_dispose'] != 'undefined', 'missing Wasm export: clang_ModuleMapDescriptor_dispose');
  assert(typeof wasmExports['clang_disposeTranslationUnit'] != 'undefined', 'missing Wasm export: clang_disposeTranslationUnit');
  assert(typeof wasmExports['clang_isInvalid'] != 'undefined', 'missing Wasm export: clang_isInvalid');
  assert(typeof wasmExports['clang_isDeclaration'] != 'undefined', 'missing Wasm export: clang_isDeclaration');
  assert(typeof wasmExports['clang_isReference'] != 'undefined', 'missing Wasm export: clang_isReference');
  assert(typeof wasmExports['clang_isStatement'] != 'undefined', 'missing Wasm export: clang_isStatement');
  assert(typeof wasmExports['clang_isExpression'] != 'undefined', 'missing Wasm export: clang_isExpression');
  assert(typeof wasmExports['clang_isTranslationUnit'] != 'undefined', 'missing Wasm export: clang_isTranslationUnit');
  assert(typeof wasmExports['clang_createIndex'] != 'undefined', 'missing Wasm export: clang_createIndex');
  assert(typeof wasmExports['clang_disposeIndex'] != 'undefined', 'missing Wasm export: clang_disposeIndex');
  assert(typeof wasmExports['clang_CXIndex_setGlobalOptions'] != 'undefined', 'missing Wasm export: clang_CXIndex_setGlobalOptions');
  assert(typeof wasmExports['clang_CXIndex_getGlobalOptions'] != 'undefined', 'missing Wasm export: clang_CXIndex_getGlobalOptions');
  assert(typeof wasmExports['clang_CXIndex_setInvocationEmissionPathOption'] != 'undefined', 'missing Wasm export: clang_CXIndex_setInvocationEmissionPathOption');
  assert(typeof wasmExports['clang_toggleCrashRecovery'] != 'undefined', 'missing Wasm export: clang_toggleCrashRecovery');
  assert(typeof wasmExports['clang_createTranslationUnit'] != 'undefined', 'missing Wasm export: clang_createTranslationUnit');
  assert(typeof wasmExports['clang_createTranslationUnit2'] != 'undefined', 'missing Wasm export: clang_createTranslationUnit2');
  assert(typeof wasmExports['clang_defaultEditingTranslationUnitOptions'] != 'undefined', 'missing Wasm export: clang_defaultEditingTranslationUnitOptions');
  assert(typeof wasmExports['clang_createTranslationUnitFromSourceFile'] != 'undefined', 'missing Wasm export: clang_createTranslationUnitFromSourceFile');
  assert(typeof wasmExports['clang_parseTranslationUnit2'] != 'undefined', 'missing Wasm export: clang_parseTranslationUnit2');
  assert(typeof wasmExports['clang_parseTranslationUnit'] != 'undefined', 'missing Wasm export: clang_parseTranslationUnit');
  assert(typeof wasmExports['clang_parseTranslationUnit2FullArgv'] != 'undefined', 'missing Wasm export: clang_parseTranslationUnit2FullArgv');
  assert(typeof wasmExports['clang_getCXTUResourceUsage'] != 'undefined', 'missing Wasm export: clang_getCXTUResourceUsage');
  assert(typeof wasmExports['clang_getTUResourceUsageName'] != 'undefined', 'missing Wasm export: clang_getTUResourceUsageName');
  assert(typeof wasmExports['clang_disposeCXTUResourceUsage'] != 'undefined', 'missing Wasm export: clang_disposeCXTUResourceUsage');
  assert(typeof wasmExports['clang_Type_getObjCEncoding'] != 'undefined', 'missing Wasm export: clang_Type_getObjCEncoding');
  assert(typeof wasmExports['clang_Cursor_isMacroFunctionLike'] != 'undefined', 'missing Wasm export: clang_Cursor_isMacroFunctionLike');
  assert(typeof wasmExports['clang_Cursor_isMacroBuiltin'] != 'undefined', 'missing Wasm export: clang_Cursor_isMacroBuiltin');
  assert(typeof wasmExports['clang_Cursor_isFunctionInlined'] != 'undefined', 'missing Wasm export: clang_Cursor_isFunctionInlined');
  assert(typeof wasmExports['clang_EvalResult_dispose'] != 'undefined', 'missing Wasm export: clang_EvalResult_dispose');
  assert(typeof wasmExports['clang_EvalResult_getKind'] != 'undefined', 'missing Wasm export: clang_EvalResult_getKind');
  assert(typeof wasmExports['clang_EvalResult_getAsInt'] != 'undefined', 'missing Wasm export: clang_EvalResult_getAsInt');
  assert(typeof wasmExports['clang_EvalResult_getAsLongLong'] != 'undefined', 'missing Wasm export: clang_EvalResult_getAsLongLong');
  assert(typeof wasmExports['clang_EvalResult_isUnsignedInt'] != 'undefined', 'missing Wasm export: clang_EvalResult_isUnsignedInt');
  assert(typeof wasmExports['clang_EvalResult_getAsUnsigned'] != 'undefined', 'missing Wasm export: clang_EvalResult_getAsUnsigned');
  assert(typeof wasmExports['clang_EvalResult_getAsDouble'] != 'undefined', 'missing Wasm export: clang_EvalResult_getAsDouble');
  assert(typeof wasmExports['clang_EvalResult_getAsStr'] != 'undefined', 'missing Wasm export: clang_EvalResult_getAsStr');
  assert(typeof wasmExports['clang_Cursor_Evaluate'] != 'undefined', 'missing Wasm export: clang_Cursor_Evaluate');
  assert(typeof wasmExports['clang_getCursorKind'] != 'undefined', 'missing Wasm export: clang_getCursorKind');
  assert(typeof wasmExports['clang_Cursor_hasAttrs'] != 'undefined', 'missing Wasm export: clang_Cursor_hasAttrs');
  assert(typeof wasmExports['clang_defaultSaveOptions'] != 'undefined', 'missing Wasm export: clang_defaultSaveOptions');
  assert(typeof wasmExports['clang_saveTranslationUnit'] != 'undefined', 'missing Wasm export: clang_saveTranslationUnit');
  assert(typeof wasmExports['clang_suspendTranslationUnit'] != 'undefined', 'missing Wasm export: clang_suspendTranslationUnit');
  assert(typeof wasmExports['clang_defaultReparseOptions'] != 'undefined', 'missing Wasm export: clang_defaultReparseOptions');
  assert(typeof wasmExports['clang_reparseTranslationUnit'] != 'undefined', 'missing Wasm export: clang_reparseTranslationUnit');
  assert(typeof wasmExports['clang_getTranslationUnitSpelling'] != 'undefined', 'missing Wasm export: clang_getTranslationUnitSpelling');
  assert(typeof wasmExports['clang_getTranslationUnitCursor'] != 'undefined', 'missing Wasm export: clang_getTranslationUnitCursor');
  assert(typeof wasmExports['clang_getNullCursor'] != 'undefined', 'missing Wasm export: clang_getNullCursor');
  assert(typeof wasmExports['clang_getTranslationUnitTargetInfo'] != 'undefined', 'missing Wasm export: clang_getTranslationUnitTargetInfo');
  assert(typeof wasmExports['clang_TargetInfo_getTriple'] != 'undefined', 'missing Wasm export: clang_TargetInfo_getTriple');
  assert(typeof wasmExports['clang_TargetInfo_getPointerWidth'] != 'undefined', 'missing Wasm export: clang_TargetInfo_getPointerWidth');
  assert(typeof wasmExports['clang_TargetInfo_dispose'] != 'undefined', 'missing Wasm export: clang_TargetInfo_dispose');
  assert(typeof wasmExports['clang_getFileName'] != 'undefined', 'missing Wasm export: clang_getFileName');
  assert(typeof wasmExports['clang_getFileTime'] != 'undefined', 'missing Wasm export: clang_getFileTime');
  assert(typeof wasmExports['clang_getFile'] != 'undefined', 'missing Wasm export: clang_getFile');
  assert(typeof wasmExports['clang_getFileContents'] != 'undefined', 'missing Wasm export: clang_getFileContents');
  assert(typeof wasmExports['clang_isFileMultipleIncludeGuarded'] != 'undefined', 'missing Wasm export: clang_isFileMultipleIncludeGuarded');
  assert(typeof wasmExports['clang_getFileUniqueID'] != 'undefined', 'missing Wasm export: clang_getFileUniqueID');
  assert(typeof wasmExports['clang_File_isEqual'] != 'undefined', 'missing Wasm export: clang_File_isEqual');
  assert(typeof wasmExports['clang_File_tryGetRealPathName'] != 'undefined', 'missing Wasm export: clang_File_tryGetRealPathName');
  assert(typeof wasmExports['clang_visitChildren'] != 'undefined', 'missing Wasm export: clang_visitChildren');
  assert(typeof wasmExports['clang_visitChildrenWithBlock'] != 'undefined', 'missing Wasm export: clang_visitChildrenWithBlock');
  assert(typeof wasmExports['clang_getCursorSpelling'] != 'undefined', 'missing Wasm export: clang_getCursorSpelling');
  assert(typeof wasmExports['clang_Cursor_getSpellingNameRange'] != 'undefined', 'missing Wasm export: clang_Cursor_getSpellingNameRange');
  assert(typeof wasmExports['clang_getCursorLocation'] != 'undefined', 'missing Wasm export: clang_getCursorLocation');
  assert(typeof wasmExports['clang_Cursor_getMangling'] != 'undefined', 'missing Wasm export: clang_Cursor_getMangling');
  assert(typeof wasmExports['clang_Cursor_getCXXManglings'] != 'undefined', 'missing Wasm export: clang_Cursor_getCXXManglings');
  assert(typeof wasmExports['clang_Cursor_getObjCManglings'] != 'undefined', 'missing Wasm export: clang_Cursor_getObjCManglings');
  assert(typeof wasmExports['clang_getCursorPrintingPolicy'] != 'undefined', 'missing Wasm export: clang_getCursorPrintingPolicy');
  assert(typeof wasmExports['clang_PrintingPolicy_dispose'] != 'undefined', 'missing Wasm export: clang_PrintingPolicy_dispose');
  assert(typeof wasmExports['clang_PrintingPolicy_getProperty'] != 'undefined', 'missing Wasm export: clang_PrintingPolicy_getProperty');
  assert(typeof wasmExports['clang_PrintingPolicy_setProperty'] != 'undefined', 'missing Wasm export: clang_PrintingPolicy_setProperty');
  assert(typeof wasmExports['clang_getCursorPrettyPrinted'] != 'undefined', 'missing Wasm export: clang_getCursorPrettyPrinted');
  assert(typeof wasmExports['clang_getCursorDisplayName'] != 'undefined', 'missing Wasm export: clang_getCursorDisplayName');
  assert(typeof wasmExports['clang_getCursorKindSpelling'] != 'undefined', 'missing Wasm export: clang_getCursorKindSpelling');
  assert(typeof wasmExports['clang_getCursor'] != 'undefined', 'missing Wasm export: clang_getCursor');
  assert(typeof wasmExports['clang_getCursorDefinition'] != 'undefined', 'missing Wasm export: clang_getCursorDefinition');
  assert(typeof wasmExports['clang_isCursorDefinition'] != 'undefined', 'missing Wasm export: clang_isCursorDefinition');
  assert(typeof wasmExports['clang_getCursorReferenced'] != 'undefined', 'missing Wasm export: clang_getCursorReferenced');
  assert(typeof wasmExports['clang_equalCursors'] != 'undefined', 'missing Wasm export: clang_equalCursors');
  assert(typeof wasmExports['clang_hashCursor'] != 'undefined', 'missing Wasm export: clang_hashCursor');
  assert(typeof wasmExports['clang_isInvalidDeclaration'] != 'undefined', 'missing Wasm export: clang_isInvalidDeclaration');
  assert(typeof wasmExports['clang_isAttribute'] != 'undefined', 'missing Wasm export: clang_isAttribute');
  assert(typeof wasmExports['clang_isPreprocessing'] != 'undefined', 'missing Wasm export: clang_isPreprocessing');
  assert(typeof wasmExports['clang_isUnexposed'] != 'undefined', 'missing Wasm export: clang_isUnexposed');
  assert(typeof wasmExports['clang_getCursorExtent'] != 'undefined', 'missing Wasm export: clang_getCursorExtent');
  assert(typeof wasmExports['clang_getCanonicalCursor'] != 'undefined', 'missing Wasm export: clang_getCanonicalCursor');
  assert(typeof wasmExports['clang_Cursor_getObjCSelectorIndex'] != 'undefined', 'missing Wasm export: clang_Cursor_getObjCSelectorIndex');
  assert(typeof wasmExports['clang_getNumOverloadedDecls'] != 'undefined', 'missing Wasm export: clang_getNumOverloadedDecls');
  assert(typeof wasmExports['clang_getOverloadedDecl'] != 'undefined', 'missing Wasm export: clang_getOverloadedDecl');
  assert(typeof wasmExports['clang_getDefinitionSpellingAndExtent'] != 'undefined', 'missing Wasm export: clang_getDefinitionSpellingAndExtent');
  assert(typeof wasmExports['clang_getCursorReferenceNameRange'] != 'undefined', 'missing Wasm export: clang_getCursorReferenceNameRange');
  assert(typeof wasmExports['clang_enableStackTraces'] != 'undefined', 'missing Wasm export: clang_enableStackTraces');
  assert(typeof wasmExports['clang_executeOnThread'] != 'undefined', 'missing Wasm export: clang_executeOnThread');
  assert(typeof wasmExports['clang_getTokenKind'] != 'undefined', 'missing Wasm export: clang_getTokenKind');
  assert(typeof wasmExports['clang_getTokenSpelling'] != 'undefined', 'missing Wasm export: clang_getTokenSpelling');
  assert(typeof wasmExports['clang_getTokenLocation'] != 'undefined', 'missing Wasm export: clang_getTokenLocation');
  assert(typeof wasmExports['clang_getTokenExtent'] != 'undefined', 'missing Wasm export: clang_getTokenExtent');
  assert(typeof wasmExports['clang_getToken'] != 'undefined', 'missing Wasm export: clang_getToken');
  assert(typeof wasmExports['clang_tokenize'] != 'undefined', 'missing Wasm export: clang_tokenize');
  assert(typeof wasmExports['clang_disposeTokens'] != 'undefined', 'missing Wasm export: clang_disposeTokens');
  assert(typeof wasmExports['clang_annotateTokens'] != 'undefined', 'missing Wasm export: clang_annotateTokens');
  assert(typeof wasmExports['clang_getCursorLinkage'] != 'undefined', 'missing Wasm export: clang_getCursorLinkage');
  assert(typeof wasmExports['clang_getCursorVisibility'] != 'undefined', 'missing Wasm export: clang_getCursorVisibility');
  assert(typeof wasmExports['clang_getCursorAvailability'] != 'undefined', 'missing Wasm export: clang_getCursorAvailability');
  assert(typeof wasmExports['clang_getCursorPlatformAvailability'] != 'undefined', 'missing Wasm export: clang_getCursorPlatformAvailability');
  assert(typeof wasmExports['clang_disposeCXPlatformAvailability'] != 'undefined', 'missing Wasm export: clang_disposeCXPlatformAvailability');
  assert(typeof wasmExports['clang_getCursorLanguage'] != 'undefined', 'missing Wasm export: clang_getCursorLanguage');
  assert(typeof wasmExports['clang_getCursorTLSKind'] != 'undefined', 'missing Wasm export: clang_getCursorTLSKind');
  assert(typeof wasmExports['clang_Cursor_getStorageClass'] != 'undefined', 'missing Wasm export: clang_Cursor_getStorageClass');
  assert(typeof wasmExports['clang_getCursorSemanticParent'] != 'undefined', 'missing Wasm export: clang_getCursorSemanticParent');
  assert(typeof wasmExports['clang_getCursorLexicalParent'] != 'undefined', 'missing Wasm export: clang_getCursorLexicalParent');
  assert(typeof wasmExports['clang_getIncludedFile'] != 'undefined', 'missing Wasm export: clang_getIncludedFile');
  assert(typeof wasmExports['clang_Cursor_getObjCPropertyAttributes'] != 'undefined', 'missing Wasm export: clang_Cursor_getObjCPropertyAttributes');
  assert(typeof wasmExports['clang_Cursor_getObjCPropertyGetterName'] != 'undefined', 'missing Wasm export: clang_Cursor_getObjCPropertyGetterName');
  assert(typeof wasmExports['clang_Cursor_getObjCPropertySetterName'] != 'undefined', 'missing Wasm export: clang_Cursor_getObjCPropertySetterName');
  assert(typeof wasmExports['clang_Cursor_getObjCDeclQualifiers'] != 'undefined', 'missing Wasm export: clang_Cursor_getObjCDeclQualifiers');
  assert(typeof wasmExports['clang_Cursor_isObjCOptional'] != 'undefined', 'missing Wasm export: clang_Cursor_isObjCOptional');
  assert(typeof wasmExports['clang_Cursor_isVariadic'] != 'undefined', 'missing Wasm export: clang_Cursor_isVariadic');
  assert(typeof wasmExports['clang_Cursor_isExternalSymbol'] != 'undefined', 'missing Wasm export: clang_Cursor_isExternalSymbol');
  assert(typeof wasmExports['clang_Cursor_getCommentRange'] != 'undefined', 'missing Wasm export: clang_Cursor_getCommentRange');
  assert(typeof wasmExports['clang_Cursor_getRawCommentText'] != 'undefined', 'missing Wasm export: clang_Cursor_getRawCommentText');
  assert(typeof wasmExports['clang_Cursor_getBriefCommentText'] != 'undefined', 'missing Wasm export: clang_Cursor_getBriefCommentText');
  assert(typeof wasmExports['clang_Cursor_getModule'] != 'undefined', 'missing Wasm export: clang_Cursor_getModule');
  assert(typeof wasmExports['clang_getModuleForFile'] != 'undefined', 'missing Wasm export: clang_getModuleForFile');
  assert(typeof wasmExports['clang_Module_getASTFile'] != 'undefined', 'missing Wasm export: clang_Module_getASTFile');
  assert(typeof wasmExports['clang_Module_getParent'] != 'undefined', 'missing Wasm export: clang_Module_getParent');
  assert(typeof wasmExports['clang_Module_getName'] != 'undefined', 'missing Wasm export: clang_Module_getName');
  assert(typeof wasmExports['clang_Module_getFullName'] != 'undefined', 'missing Wasm export: clang_Module_getFullName');
  assert(typeof wasmExports['clang_Module_isSystem'] != 'undefined', 'missing Wasm export: clang_Module_isSystem');
  assert(typeof wasmExports['clang_Module_getNumTopLevelHeaders'] != 'undefined', 'missing Wasm export: clang_Module_getNumTopLevelHeaders');
  assert(typeof wasmExports['clang_Module_getTopLevelHeader'] != 'undefined', 'missing Wasm export: clang_Module_getTopLevelHeader');
  assert(typeof wasmExports['clang_CXXConstructor_isDefaultConstructor'] != 'undefined', 'missing Wasm export: clang_CXXConstructor_isDefaultConstructor');
  assert(typeof wasmExports['clang_CXXConstructor_isCopyConstructor'] != 'undefined', 'missing Wasm export: clang_CXXConstructor_isCopyConstructor');
  assert(typeof wasmExports['clang_CXXConstructor_isMoveConstructor'] != 'undefined', 'missing Wasm export: clang_CXXConstructor_isMoveConstructor');
  assert(typeof wasmExports['clang_CXXConstructor_isConvertingConstructor'] != 'undefined', 'missing Wasm export: clang_CXXConstructor_isConvertingConstructor');
  assert(typeof wasmExports['clang_CXXField_isMutable'] != 'undefined', 'missing Wasm export: clang_CXXField_isMutable');
  assert(typeof wasmExports['clang_CXXMethod_isPureVirtual'] != 'undefined', 'missing Wasm export: clang_CXXMethod_isPureVirtual');
  assert(typeof wasmExports['clang_CXXMethod_isConst'] != 'undefined', 'missing Wasm export: clang_CXXMethod_isConst');
  assert(typeof wasmExports['clang_CXXMethod_isDefaulted'] != 'undefined', 'missing Wasm export: clang_CXXMethod_isDefaulted');
  assert(typeof wasmExports['clang_CXXMethod_isStatic'] != 'undefined', 'missing Wasm export: clang_CXXMethod_isStatic');
  assert(typeof wasmExports['clang_CXXMethod_isVirtual'] != 'undefined', 'missing Wasm export: clang_CXXMethod_isVirtual');
  assert(typeof wasmExports['clang_CXXRecord_isAbstract'] != 'undefined', 'missing Wasm export: clang_CXXRecord_isAbstract');
  assert(typeof wasmExports['clang_EnumDecl_isScoped'] != 'undefined', 'missing Wasm export: clang_EnumDecl_isScoped');
  assert(typeof wasmExports['clang_getIBOutletCollectionType'] != 'undefined', 'missing Wasm export: clang_getIBOutletCollectionType');
  assert(typeof wasmExports['clang_getSkippedRanges'] != 'undefined', 'missing Wasm export: clang_getSkippedRanges');
  assert(typeof wasmExports['clang_getAllSkippedRanges'] != 'undefined', 'missing Wasm export: clang_getAllSkippedRanges');
  assert(typeof wasmExports['clang_disposeSourceRangeList'] != 'undefined', 'missing Wasm export: clang_disposeSourceRangeList');
  assert(typeof wasmExports['clang_Cursor_getVarDeclInitializer'] != 'undefined', 'missing Wasm export: clang_Cursor_getVarDeclInitializer');
  assert(typeof wasmExports['clang_Cursor_hasVarDeclGlobalStorage'] != 'undefined', 'missing Wasm export: clang_Cursor_hasVarDeclGlobalStorage');
  assert(typeof wasmExports['clang_Cursor_hasVarDeclExternalStorage'] != 'undefined', 'missing Wasm export: clang_Cursor_hasVarDeclExternalStorage');
  assert(typeof wasmExports['clang_getClangVersion'] != 'undefined', 'missing Wasm export: clang_getClangVersion');
  assert(typeof wasmExports['clang_isVirtualBase'] != 'undefined', 'missing Wasm export: clang_isVirtualBase');
  assert(typeof wasmExports['clang_getCXXAccessSpecifier'] != 'undefined', 'missing Wasm export: clang_getCXXAccessSpecifier');
  assert(typeof wasmExports['clang_getTemplateCursorKind'] != 'undefined', 'missing Wasm export: clang_getTemplateCursorKind');
  assert(typeof wasmExports['clang_getSpecializedCursorTemplate'] != 'undefined', 'missing Wasm export: clang_getSpecializedCursorTemplate');
  assert(typeof wasmExports['clang_getCompletionChunkKind'] != 'undefined', 'missing Wasm export: clang_getCompletionChunkKind');
  assert(typeof wasmExports['clang_getCompletionChunkText'] != 'undefined', 'missing Wasm export: clang_getCompletionChunkText');
  assert(typeof wasmExports['clang_getCompletionChunkCompletionString'] != 'undefined', 'missing Wasm export: clang_getCompletionChunkCompletionString');
  assert(typeof wasmExports['clang_getNumCompletionChunks'] != 'undefined', 'missing Wasm export: clang_getNumCompletionChunks');
  assert(typeof wasmExports['clang_getCompletionPriority'] != 'undefined', 'missing Wasm export: clang_getCompletionPriority');
  assert(typeof wasmExports['clang_getCompletionAvailability'] != 'undefined', 'missing Wasm export: clang_getCompletionAvailability');
  assert(typeof wasmExports['clang_getCompletionNumAnnotations'] != 'undefined', 'missing Wasm export: clang_getCompletionNumAnnotations');
  assert(typeof wasmExports['clang_getCompletionAnnotation'] != 'undefined', 'missing Wasm export: clang_getCompletionAnnotation');
  assert(typeof wasmExports['clang_getCompletionParent'] != 'undefined', 'missing Wasm export: clang_getCompletionParent');
  assert(typeof wasmExports['clang_getCompletionBriefComment'] != 'undefined', 'missing Wasm export: clang_getCompletionBriefComment');
  assert(typeof wasmExports['clang_getCompletionNumFixIts'] != 'undefined', 'missing Wasm export: clang_getCompletionNumFixIts');
  assert(typeof wasmExports['clang_getCompletionFixIt'] != 'undefined', 'missing Wasm export: clang_getCompletionFixIt');
  assert(typeof wasmExports['clang_codeCompleteAt'] != 'undefined', 'missing Wasm export: clang_codeCompleteAt');
  assert(typeof wasmExports['clang_defaultCodeCompleteOptions'] != 'undefined', 'missing Wasm export: clang_defaultCodeCompleteOptions');
  assert(typeof wasmExports['clang_disposeCodeCompleteResults'] != 'undefined', 'missing Wasm export: clang_disposeCodeCompleteResults');
  assert(typeof wasmExports['clang_codeCompleteGetNumDiagnostics'] != 'undefined', 'missing Wasm export: clang_codeCompleteGetNumDiagnostics');
  assert(typeof wasmExports['clang_codeCompleteGetDiagnostic'] != 'undefined', 'missing Wasm export: clang_codeCompleteGetDiagnostic');
  assert(typeof wasmExports['clang_codeCompleteGetContexts'] != 'undefined', 'missing Wasm export: clang_codeCompleteGetContexts');
  assert(typeof wasmExports['clang_codeCompleteGetContainerKind'] != 'undefined', 'missing Wasm export: clang_codeCompleteGetContainerKind');
  assert(typeof wasmExports['clang_codeCompleteGetContainerUSR'] != 'undefined', 'missing Wasm export: clang_codeCompleteGetContainerUSR');
  assert(typeof wasmExports['clang_codeCompleteGetObjCSelector'] != 'undefined', 'missing Wasm export: clang_codeCompleteGetObjCSelector');
  assert(typeof wasmExports['clang_sortCodeCompletionResults'] != 'undefined', 'missing Wasm export: clang_sortCodeCompletionResults');
  assert(typeof wasmExports['clang_getNumDiagnostics'] != 'undefined', 'missing Wasm export: clang_getNumDiagnostics');
  assert(typeof wasmExports['clang_getDiagnostic'] != 'undefined', 'missing Wasm export: clang_getDiagnostic');
  assert(typeof wasmExports['clang_getDiagnosticSetFromTU'] != 'undefined', 'missing Wasm export: clang_getDiagnosticSetFromTU');
  assert(typeof wasmExports['clang_disposeDiagnostic'] != 'undefined', 'missing Wasm export: clang_disposeDiagnostic');
  assert(typeof wasmExports['clang_formatDiagnostic'] != 'undefined', 'missing Wasm export: clang_formatDiagnostic');
  assert(typeof wasmExports['clang_getDiagnosticRange'] != 'undefined', 'missing Wasm export: clang_getDiagnosticRange');
  assert(typeof wasmExports['clang_getDiagnosticSeverity'] != 'undefined', 'missing Wasm export: clang_getDiagnosticSeverity');
  assert(typeof wasmExports['clang_getDiagnosticLocation'] != 'undefined', 'missing Wasm export: clang_getDiagnosticLocation');
  assert(typeof wasmExports['clang_getDiagnosticNumRanges'] != 'undefined', 'missing Wasm export: clang_getDiagnosticNumRanges');
  assert(typeof wasmExports['clang_getDiagnosticSpelling'] != 'undefined', 'missing Wasm export: clang_getDiagnosticSpelling');
  assert(typeof wasmExports['clang_getDiagnosticOption'] != 'undefined', 'missing Wasm export: clang_getDiagnosticOption');
  assert(typeof wasmExports['clang_getDiagnosticCategory'] != 'undefined', 'missing Wasm export: clang_getDiagnosticCategory');
  assert(typeof wasmExports['clang_getDiagnosticCategoryText'] != 'undefined', 'missing Wasm export: clang_getDiagnosticCategoryText');
  assert(typeof wasmExports['clang_defaultDiagnosticDisplayOptions'] != 'undefined', 'missing Wasm export: clang_defaultDiagnosticDisplayOptions');
  assert(typeof wasmExports['clang_getDiagnosticCategoryName'] != 'undefined', 'missing Wasm export: clang_getDiagnosticCategoryName');
  assert(typeof wasmExports['clang_getDiagnosticNumFixIts'] != 'undefined', 'missing Wasm export: clang_getDiagnosticNumFixIts');
  assert(typeof wasmExports['clang_getDiagnosticFixIt'] != 'undefined', 'missing Wasm export: clang_getDiagnosticFixIt');
  assert(typeof wasmExports['clang_disposeDiagnosticSet'] != 'undefined', 'missing Wasm export: clang_disposeDiagnosticSet');
  assert(typeof wasmExports['clang_getDiagnosticInSet'] != 'undefined', 'missing Wasm export: clang_getDiagnosticInSet');
  assert(typeof wasmExports['clang_getChildDiagnostics'] != 'undefined', 'missing Wasm export: clang_getChildDiagnostics');
  assert(typeof wasmExports['clang_getNumDiagnosticsInSet'] != 'undefined', 'missing Wasm export: clang_getNumDiagnosticsInSet');
  assert(typeof wasmExports['clang_findReferencesInFile'] != 'undefined', 'missing Wasm export: clang_findReferencesInFile');
  assert(typeof wasmExports['clang_findIncludesInFile'] != 'undefined', 'missing Wasm export: clang_findIncludesInFile');
  assert(typeof wasmExports['clang_findReferencesInFileWithBlock'] != 'undefined', 'missing Wasm export: clang_findReferencesInFileWithBlock');
  assert(typeof wasmExports['clang_findIncludesInFileWithBlock'] != 'undefined', 'missing Wasm export: clang_findIncludesInFileWithBlock');
  assert(typeof wasmExports['clang_getInclusions'] != 'undefined', 'missing Wasm export: clang_getInclusions');
  assert(typeof wasmExports['clang_getCursorUSR'] != 'undefined', 'missing Wasm export: clang_getCursorUSR');
  assert(typeof wasmExports['clang_constructUSR_ObjCIvar'] != 'undefined', 'missing Wasm export: clang_constructUSR_ObjCIvar');
  assert(typeof wasmExports['clang_constructUSR_ObjCMethod'] != 'undefined', 'missing Wasm export: clang_constructUSR_ObjCMethod');
  assert(typeof wasmExports['clang_constructUSR_ObjCClass'] != 'undefined', 'missing Wasm export: clang_constructUSR_ObjCClass');
  assert(typeof wasmExports['clang_constructUSR_ObjCProtocol'] != 'undefined', 'missing Wasm export: clang_constructUSR_ObjCProtocol');
  assert(typeof wasmExports['clang_constructUSR_ObjCCategory'] != 'undefined', 'missing Wasm export: clang_constructUSR_ObjCCategory');
  assert(typeof wasmExports['clang_constructUSR_ObjCProperty'] != 'undefined', 'missing Wasm export: clang_constructUSR_ObjCProperty');
  assert(typeof wasmExports['clang_Cursor_getParsedComment'] != 'undefined', 'missing Wasm export: clang_Cursor_getParsedComment');
  assert(typeof wasmExports['clang_Comment_getKind'] != 'undefined', 'missing Wasm export: clang_Comment_getKind');
  assert(typeof wasmExports['clang_Comment_getNumChildren'] != 'undefined', 'missing Wasm export: clang_Comment_getNumChildren');
  assert(typeof wasmExports['clang_Comment_getChild'] != 'undefined', 'missing Wasm export: clang_Comment_getChild');
  assert(typeof wasmExports['clang_Comment_isWhitespace'] != 'undefined', 'missing Wasm export: clang_Comment_isWhitespace');
  assert(typeof wasmExports['clang_InlineContentComment_hasTrailingNewline'] != 'undefined', 'missing Wasm export: clang_InlineContentComment_hasTrailingNewline');
  assert(typeof wasmExports['clang_TextComment_getText'] != 'undefined', 'missing Wasm export: clang_TextComment_getText');
  assert(typeof wasmExports['clang_InlineCommandComment_getCommandName'] != 'undefined', 'missing Wasm export: clang_InlineCommandComment_getCommandName');
  assert(typeof wasmExports['clang_InlineCommandComment_getRenderKind'] != 'undefined', 'missing Wasm export: clang_InlineCommandComment_getRenderKind');
  assert(typeof wasmExports['clang_InlineCommandComment_getNumArgs'] != 'undefined', 'missing Wasm export: clang_InlineCommandComment_getNumArgs');
  assert(typeof wasmExports['clang_InlineCommandComment_getArgText'] != 'undefined', 'missing Wasm export: clang_InlineCommandComment_getArgText');
  assert(typeof wasmExports['clang_HTMLTagComment_getTagName'] != 'undefined', 'missing Wasm export: clang_HTMLTagComment_getTagName');
  assert(typeof wasmExports['clang_HTMLStartTagComment_isSelfClosing'] != 'undefined', 'missing Wasm export: clang_HTMLStartTagComment_isSelfClosing');
  assert(typeof wasmExports['clang_HTMLStartTag_getNumAttrs'] != 'undefined', 'missing Wasm export: clang_HTMLStartTag_getNumAttrs');
  assert(typeof wasmExports['clang_HTMLStartTag_getAttrName'] != 'undefined', 'missing Wasm export: clang_HTMLStartTag_getAttrName');
  assert(typeof wasmExports['clang_HTMLStartTag_getAttrValue'] != 'undefined', 'missing Wasm export: clang_HTMLStartTag_getAttrValue');
  assert(typeof wasmExports['clang_BlockCommandComment_getCommandName'] != 'undefined', 'missing Wasm export: clang_BlockCommandComment_getCommandName');
  assert(typeof wasmExports['clang_BlockCommandComment_getNumArgs'] != 'undefined', 'missing Wasm export: clang_BlockCommandComment_getNumArgs');
  assert(typeof wasmExports['clang_BlockCommandComment_getArgText'] != 'undefined', 'missing Wasm export: clang_BlockCommandComment_getArgText');
  assert(typeof wasmExports['clang_BlockCommandComment_getParagraph'] != 'undefined', 'missing Wasm export: clang_BlockCommandComment_getParagraph');
  assert(typeof wasmExports['clang_ParamCommandComment_getParamName'] != 'undefined', 'missing Wasm export: clang_ParamCommandComment_getParamName');
  assert(typeof wasmExports['clang_ParamCommandComment_isParamIndexValid'] != 'undefined', 'missing Wasm export: clang_ParamCommandComment_isParamIndexValid');
  assert(typeof wasmExports['clang_ParamCommandComment_getParamIndex'] != 'undefined', 'missing Wasm export: clang_ParamCommandComment_getParamIndex');
  assert(typeof wasmExports['clang_ParamCommandComment_isDirectionExplicit'] != 'undefined', 'missing Wasm export: clang_ParamCommandComment_isDirectionExplicit');
  assert(typeof wasmExports['clang_ParamCommandComment_getDirection'] != 'undefined', 'missing Wasm export: clang_ParamCommandComment_getDirection');
  assert(typeof wasmExports['clang_TParamCommandComment_getParamName'] != 'undefined', 'missing Wasm export: clang_TParamCommandComment_getParamName');
  assert(typeof wasmExports['clang_TParamCommandComment_isParamPositionValid'] != 'undefined', 'missing Wasm export: clang_TParamCommandComment_isParamPositionValid');
  assert(typeof wasmExports['clang_TParamCommandComment_getDepth'] != 'undefined', 'missing Wasm export: clang_TParamCommandComment_getDepth');
  assert(typeof wasmExports['clang_TParamCommandComment_getIndex'] != 'undefined', 'missing Wasm export: clang_TParamCommandComment_getIndex');
  assert(typeof wasmExports['clang_VerbatimBlockLineComment_getText'] != 'undefined', 'missing Wasm export: clang_VerbatimBlockLineComment_getText');
  assert(typeof wasmExports['clang_VerbatimLineComment_getText'] != 'undefined', 'missing Wasm export: clang_VerbatimLineComment_getText');
  assert(typeof wasmExports['clang_HTMLTagComment_getAsString'] != 'undefined', 'missing Wasm export: clang_HTMLTagComment_getAsString');
  assert(typeof wasmExports['clang_FullComment_getAsHTML'] != 'undefined', 'missing Wasm export: clang_FullComment_getAsHTML');
  assert(typeof wasmExports['clang_FullComment_getAsXML'] != 'undefined', 'missing Wasm export: clang_FullComment_getAsXML');
  assert(typeof wasmExports['clang_Cursor_isNull'] != 'undefined', 'missing Wasm export: clang_Cursor_isNull');
  assert(typeof wasmExports['clang_Cursor_getTranslationUnit'] != 'undefined', 'missing Wasm export: clang_Cursor_getTranslationUnit');
  assert(typeof wasmExports['clang_Cursor_getNumArguments'] != 'undefined', 'missing Wasm export: clang_Cursor_getNumArguments');
  assert(typeof wasmExports['clang_Cursor_getArgument'] != 'undefined', 'missing Wasm export: clang_Cursor_getArgument');
  assert(typeof wasmExports['clang_Cursor_getNumTemplateArguments'] != 'undefined', 'missing Wasm export: clang_Cursor_getNumTemplateArguments');
  assert(typeof wasmExports['clang_Cursor_getTemplateArgumentKind'] != 'undefined', 'missing Wasm export: clang_Cursor_getTemplateArgumentKind');
  assert(typeof wasmExports['clang_Cursor_getTemplateArgumentType'] != 'undefined', 'missing Wasm export: clang_Cursor_getTemplateArgumentType');
  assert(typeof wasmExports['clang_Cursor_getTemplateArgumentValue'] != 'undefined', 'missing Wasm export: clang_Cursor_getTemplateArgumentValue');
  assert(typeof wasmExports['clang_Cursor_getTemplateArgumentUnsignedValue'] != 'undefined', 'missing Wasm export: clang_Cursor_getTemplateArgumentUnsignedValue');
  assert(typeof wasmExports['clang_createCXCursorSet'] != 'undefined', 'missing Wasm export: clang_createCXCursorSet');
  assert(typeof wasmExports['clang_disposeCXCursorSet'] != 'undefined', 'missing Wasm export: clang_disposeCXCursorSet');
  assert(typeof wasmExports['clang_CXCursorSet_contains'] != 'undefined', 'missing Wasm export: clang_CXCursorSet_contains');
  assert(typeof wasmExports['clang_CXCursorSet_insert'] != 'undefined', 'missing Wasm export: clang_CXCursorSet_insert');
  assert(typeof wasmExports['clang_getCursorCompletionString'] != 'undefined', 'missing Wasm export: clang_getCursorCompletionString');
  assert(typeof wasmExports['clang_getOverriddenCursors'] != 'undefined', 'missing Wasm export: clang_getOverriddenCursors');
  assert(typeof wasmExports['clang_disposeOverriddenCursors'] != 'undefined', 'missing Wasm export: clang_disposeOverriddenCursors');
  assert(typeof wasmExports['clang_Cursor_isDynamicCall'] != 'undefined', 'missing Wasm export: clang_Cursor_isDynamicCall');
  assert(typeof wasmExports['clang_Cursor_getReceiverType'] != 'undefined', 'missing Wasm export: clang_Cursor_getReceiverType');
  assert(typeof wasmExports['clang_CompilationDatabase_fromDirectory'] != 'undefined', 'missing Wasm export: clang_CompilationDatabase_fromDirectory');
  assert(typeof wasmExports['clang_CompilationDatabase_dispose'] != 'undefined', 'missing Wasm export: clang_CompilationDatabase_dispose');
  assert(typeof wasmExports['clang_CompilationDatabase_getCompileCommands'] != 'undefined', 'missing Wasm export: clang_CompilationDatabase_getCompileCommands');
  assert(typeof wasmExports['clang_CompilationDatabase_getAllCompileCommands'] != 'undefined', 'missing Wasm export: clang_CompilationDatabase_getAllCompileCommands');
  assert(typeof wasmExports['clang_CompileCommands_dispose'] != 'undefined', 'missing Wasm export: clang_CompileCommands_dispose');
  assert(typeof wasmExports['clang_CompileCommands_getSize'] != 'undefined', 'missing Wasm export: clang_CompileCommands_getSize');
  assert(typeof wasmExports['clang_CompileCommands_getCommand'] != 'undefined', 'missing Wasm export: clang_CompileCommands_getCommand');
  assert(typeof wasmExports['clang_CompileCommand_getDirectory'] != 'undefined', 'missing Wasm export: clang_CompileCommand_getDirectory');
  assert(typeof wasmExports['clang_CompileCommand_getFilename'] != 'undefined', 'missing Wasm export: clang_CompileCommand_getFilename');
  assert(typeof wasmExports['clang_CompileCommand_getNumArgs'] != 'undefined', 'missing Wasm export: clang_CompileCommand_getNumArgs');
  assert(typeof wasmExports['clang_CompileCommand_getArg'] != 'undefined', 'missing Wasm export: clang_CompileCommand_getArg');
  assert(typeof wasmExports['clang_CompileCommand_getNumMappedSources'] != 'undefined', 'missing Wasm export: clang_CompileCommand_getNumMappedSources');
  assert(typeof wasmExports['clang_CompileCommand_getMappedSourcePath'] != 'undefined', 'missing Wasm export: clang_CompileCommand_getMappedSourcePath');
  assert(typeof wasmExports['clang_CompileCommand_getMappedSourceContent'] != 'undefined', 'missing Wasm export: clang_CompileCommand_getMappedSourceContent');
  assert(typeof wasmExports['clang_loadDiagnostics'] != 'undefined', 'missing Wasm export: clang_loadDiagnostics');
  assert(typeof wasmExports['clang_getNullLocation'] != 'undefined', 'missing Wasm export: clang_getNullLocation');
  assert(typeof wasmExports['clang_equalLocations'] != 'undefined', 'missing Wasm export: clang_equalLocations');
  assert(typeof wasmExports['clang_getNullRange'] != 'undefined', 'missing Wasm export: clang_getNullRange');
  assert(typeof wasmExports['clang_getRange'] != 'undefined', 'missing Wasm export: clang_getRange');
  assert(typeof wasmExports['clang_equalRanges'] != 'undefined', 'missing Wasm export: clang_equalRanges');
  assert(typeof wasmExports['clang_Range_isNull'] != 'undefined', 'missing Wasm export: clang_Range_isNull');
  assert(typeof wasmExports['clang_getRangeStart'] != 'undefined', 'missing Wasm export: clang_getRangeStart');
  assert(typeof wasmExports['clang_getRangeEnd'] != 'undefined', 'missing Wasm export: clang_getRangeEnd');
  assert(typeof wasmExports['clang_getLocation'] != 'undefined', 'missing Wasm export: clang_getLocation');
  assert(typeof wasmExports['clang_getLocationForOffset'] != 'undefined', 'missing Wasm export: clang_getLocationForOffset');
  assert(typeof wasmExports['clang_Location_isInSystemHeader'] != 'undefined', 'missing Wasm export: clang_Location_isInSystemHeader');
  assert(typeof wasmExports['clang_Location_isFromMainFile'] != 'undefined', 'missing Wasm export: clang_Location_isFromMainFile');
  assert(typeof wasmExports['clang_getExpansionLocation'] != 'undefined', 'missing Wasm export: clang_getExpansionLocation');
  assert(typeof wasmExports['clang_getPresumedLocation'] != 'undefined', 'missing Wasm export: clang_getPresumedLocation');
  assert(typeof wasmExports['clang_getInstantiationLocation'] != 'undefined', 'missing Wasm export: clang_getInstantiationLocation');
  assert(typeof wasmExports['clang_getSpellingLocation'] != 'undefined', 'missing Wasm export: clang_getSpellingLocation');
  assert(typeof wasmExports['clang_getFileLocation'] != 'undefined', 'missing Wasm export: clang_getFileLocation');
  assert(typeof wasmExports['clang_getCString'] != 'undefined', 'missing Wasm export: clang_getCString');
  assert(typeof wasmExports['clang_disposeString'] != 'undefined', 'missing Wasm export: clang_disposeString');
  assert(typeof wasmExports['clang_disposeStringSet'] != 'undefined', 'missing Wasm export: clang_disposeStringSet');
  assert(typeof wasmExports['clang_getCursorType'] != 'undefined', 'missing Wasm export: clang_getCursorType');
  assert(typeof wasmExports['clang_getTypeSpelling'] != 'undefined', 'missing Wasm export: clang_getTypeSpelling');
  assert(typeof wasmExports['clang_getTypedefDeclUnderlyingType'] != 'undefined', 'missing Wasm export: clang_getTypedefDeclUnderlyingType');
  assert(typeof wasmExports['clang_getEnumDeclIntegerType'] != 'undefined', 'missing Wasm export: clang_getEnumDeclIntegerType');
  assert(typeof wasmExports['clang_getEnumConstantDeclValue'] != 'undefined', 'missing Wasm export: clang_getEnumConstantDeclValue');
  assert(typeof wasmExports['clang_getEnumConstantDeclUnsignedValue'] != 'undefined', 'missing Wasm export: clang_getEnumConstantDeclUnsignedValue');
  assert(typeof wasmExports['clang_getFieldDeclBitWidth'] != 'undefined', 'missing Wasm export: clang_getFieldDeclBitWidth');
  assert(typeof wasmExports['clang_getCanonicalType'] != 'undefined', 'missing Wasm export: clang_getCanonicalType');
  assert(typeof wasmExports['clang_isConstQualifiedType'] != 'undefined', 'missing Wasm export: clang_isConstQualifiedType');
  assert(typeof wasmExports['clang_isVolatileQualifiedType'] != 'undefined', 'missing Wasm export: clang_isVolatileQualifiedType');
  assert(typeof wasmExports['clang_isRestrictQualifiedType'] != 'undefined', 'missing Wasm export: clang_isRestrictQualifiedType');
  assert(typeof wasmExports['clang_getAddressSpace'] != 'undefined', 'missing Wasm export: clang_getAddressSpace');
  assert(typeof wasmExports['clang_getTypedefName'] != 'undefined', 'missing Wasm export: clang_getTypedefName');
  assert(typeof wasmExports['clang_getPointeeType'] != 'undefined', 'missing Wasm export: clang_getPointeeType');
  assert(typeof wasmExports['clang_getTypeDeclaration'] != 'undefined', 'missing Wasm export: clang_getTypeDeclaration');
  assert(typeof wasmExports['clang_getTypeKindSpelling'] != 'undefined', 'missing Wasm export: clang_getTypeKindSpelling');
  assert(typeof wasmExports['clang_equalTypes'] != 'undefined', 'missing Wasm export: clang_equalTypes');
  assert(typeof wasmExports['clang_isFunctionTypeVariadic'] != 'undefined', 'missing Wasm export: clang_isFunctionTypeVariadic');
  assert(typeof wasmExports['clang_getFunctionTypeCallingConv'] != 'undefined', 'missing Wasm export: clang_getFunctionTypeCallingConv');
  assert(typeof wasmExports['clang_getNumArgTypes'] != 'undefined', 'missing Wasm export: clang_getNumArgTypes');
  assert(typeof wasmExports['clang_getArgType'] != 'undefined', 'missing Wasm export: clang_getArgType');
  assert(typeof wasmExports['clang_getResultType'] != 'undefined', 'missing Wasm export: clang_getResultType');
  assert(typeof wasmExports['clang_getCursorResultType'] != 'undefined', 'missing Wasm export: clang_getCursorResultType');
  assert(typeof wasmExports['clang_getExceptionSpecificationType'] != 'undefined', 'missing Wasm export: clang_getExceptionSpecificationType');
  assert(typeof wasmExports['clang_getCursorExceptionSpecificationType'] != 'undefined', 'missing Wasm export: clang_getCursorExceptionSpecificationType');
  assert(typeof wasmExports['clang_isPODType'] != 'undefined', 'missing Wasm export: clang_isPODType');
  assert(typeof wasmExports['clang_getElementType'] != 'undefined', 'missing Wasm export: clang_getElementType');
  assert(typeof wasmExports['clang_getNumElements'] != 'undefined', 'missing Wasm export: clang_getNumElements');
  assert(typeof wasmExports['clang_getArrayElementType'] != 'undefined', 'missing Wasm export: clang_getArrayElementType');
  assert(typeof wasmExports['clang_getArraySize'] != 'undefined', 'missing Wasm export: clang_getArraySize');
  assert(typeof wasmExports['clang_Type_getAlignOf'] != 'undefined', 'missing Wasm export: clang_Type_getAlignOf');
  assert(typeof wasmExports['clang_Type_getClassType'] != 'undefined', 'missing Wasm export: clang_Type_getClassType');
  assert(typeof wasmExports['clang_Type_getSizeOf'] != 'undefined', 'missing Wasm export: clang_Type_getSizeOf');
  assert(typeof wasmExports['clang_Type_getOffsetOf'] != 'undefined', 'missing Wasm export: clang_Type_getOffsetOf');
  assert(typeof wasmExports['clang_Type_getModifiedType'] != 'undefined', 'missing Wasm export: clang_Type_getModifiedType');
  assert(typeof wasmExports['clang_Cursor_getOffsetOfField'] != 'undefined', 'missing Wasm export: clang_Cursor_getOffsetOfField');
  assert(typeof wasmExports['clang_Type_getCXXRefQualifier'] != 'undefined', 'missing Wasm export: clang_Type_getCXXRefQualifier');
  assert(typeof wasmExports['clang_Cursor_isBitField'] != 'undefined', 'missing Wasm export: clang_Cursor_isBitField');
  assert(typeof wasmExports['clang_getDeclObjCTypeEncoding'] != 'undefined', 'missing Wasm export: clang_getDeclObjCTypeEncoding');
  assert(typeof wasmExports['clang_Type_getNumTemplateArguments'] != 'undefined', 'missing Wasm export: clang_Type_getNumTemplateArguments');
  assert(typeof wasmExports['clang_Type_getTemplateArgumentAsType'] != 'undefined', 'missing Wasm export: clang_Type_getTemplateArgumentAsType');
  assert(typeof wasmExports['clang_Type_getObjCObjectBaseType'] != 'undefined', 'missing Wasm export: clang_Type_getObjCObjectBaseType');
  assert(typeof wasmExports['clang_Type_getNumObjCProtocolRefs'] != 'undefined', 'missing Wasm export: clang_Type_getNumObjCProtocolRefs');
  assert(typeof wasmExports['clang_Type_getObjCProtocolDecl'] != 'undefined', 'missing Wasm export: clang_Type_getObjCProtocolDecl');
  assert(typeof wasmExports['clang_Type_getNumObjCTypeArgs'] != 'undefined', 'missing Wasm export: clang_Type_getNumObjCTypeArgs');
  assert(typeof wasmExports['clang_Type_getObjCTypeArg'] != 'undefined', 'missing Wasm export: clang_Type_getObjCTypeArg');
  assert(typeof wasmExports['clang_Type_visitFields'] != 'undefined', 'missing Wasm export: clang_Type_visitFields');
  assert(typeof wasmExports['clang_Cursor_isAnonymous'] != 'undefined', 'missing Wasm export: clang_Cursor_isAnonymous');
  assert(typeof wasmExports['clang_Cursor_isAnonymousRecordDecl'] != 'undefined', 'missing Wasm export: clang_Cursor_isAnonymousRecordDecl');
  assert(typeof wasmExports['clang_Cursor_isInlineNamespace'] != 'undefined', 'missing Wasm export: clang_Cursor_isInlineNamespace');
  assert(typeof wasmExports['clang_Type_getNamedType'] != 'undefined', 'missing Wasm export: clang_Type_getNamedType');
  assert(typeof wasmExports['clang_Type_isTransparentTagTypedef'] != 'undefined', 'missing Wasm export: clang_Type_isTransparentTagTypedef');
  assert(typeof wasmExports['clang_Type_getNullability'] != 'undefined', 'missing Wasm export: clang_Type_getNullability');
  assert(typeof wasmExports['clang_Type_getValueType'] != 'undefined', 'missing Wasm export: clang_Type_getValueType');
  assert(typeof wasmExports['clang_index_isEntityObjCContainerKind'] != 'undefined', 'missing Wasm export: clang_index_isEntityObjCContainerKind');
  assert(typeof wasmExports['clang_index_getObjCContainerDeclInfo'] != 'undefined', 'missing Wasm export: clang_index_getObjCContainerDeclInfo');
  assert(typeof wasmExports['clang_index_getObjCInterfaceDeclInfo'] != 'undefined', 'missing Wasm export: clang_index_getObjCInterfaceDeclInfo');
  assert(typeof wasmExports['clang_index_getObjCCategoryDeclInfo'] != 'undefined', 'missing Wasm export: clang_index_getObjCCategoryDeclInfo');
  assert(typeof wasmExports['clang_index_getObjCProtocolRefListInfo'] != 'undefined', 'missing Wasm export: clang_index_getObjCProtocolRefListInfo');
  assert(typeof wasmExports['clang_index_getObjCPropertyDeclInfo'] != 'undefined', 'missing Wasm export: clang_index_getObjCPropertyDeclInfo');
  assert(typeof wasmExports['clang_index_getIBOutletCollectionAttrInfo'] != 'undefined', 'missing Wasm export: clang_index_getIBOutletCollectionAttrInfo');
  assert(typeof wasmExports['clang_index_getCXXClassDeclInfo'] != 'undefined', 'missing Wasm export: clang_index_getCXXClassDeclInfo');
  assert(typeof wasmExports['clang_index_getClientContainer'] != 'undefined', 'missing Wasm export: clang_index_getClientContainer');
  assert(typeof wasmExports['clang_index_setClientContainer'] != 'undefined', 'missing Wasm export: clang_index_setClientContainer');
  assert(typeof wasmExports['clang_index_getClientEntity'] != 'undefined', 'missing Wasm export: clang_index_getClientEntity');
  assert(typeof wasmExports['clang_index_setClientEntity'] != 'undefined', 'missing Wasm export: clang_index_setClientEntity');
  assert(typeof wasmExports['clang_IndexAction_create'] != 'undefined', 'missing Wasm export: clang_IndexAction_create');
  assert(typeof wasmExports['clang_IndexAction_dispose'] != 'undefined', 'missing Wasm export: clang_IndexAction_dispose');
  assert(typeof wasmExports['clang_indexSourceFile'] != 'undefined', 'missing Wasm export: clang_indexSourceFile');
  assert(typeof wasmExports['clang_indexSourceFileFullArgv'] != 'undefined', 'missing Wasm export: clang_indexSourceFileFullArgv');
  assert(typeof wasmExports['clang_indexTranslationUnit'] != 'undefined', 'missing Wasm export: clang_indexTranslationUnit');
  assert(typeof wasmExports['clang_indexLoc_getFileLocation'] != 'undefined', 'missing Wasm export: clang_indexLoc_getFileLocation');
  assert(typeof wasmExports['clang_indexLoc_getCXSourceLocation'] != 'undefined', 'missing Wasm export: clang_indexLoc_getCXSourceLocation');
  assert(typeof wasmExports['clang_install_aborting_llvm_fatal_error_handler'] != 'undefined', 'missing Wasm export: clang_install_aborting_llvm_fatal_error_handler');
  assert(typeof wasmExports['clang_uninstall_llvm_fatal_error_handler'] != 'undefined', 'missing Wasm export: clang_uninstall_llvm_fatal_error_handler');
  assert(typeof wasmExports['clang_CXRewriter_create'] != 'undefined', 'missing Wasm export: clang_CXRewriter_create');
  assert(typeof wasmExports['clang_CXRewriter_insertTextBefore'] != 'undefined', 'missing Wasm export: clang_CXRewriter_insertTextBefore');
  assert(typeof wasmExports['clang_CXRewriter_replaceText'] != 'undefined', 'missing Wasm export: clang_CXRewriter_replaceText');
  assert(typeof wasmExports['clang_CXRewriter_removeText'] != 'undefined', 'missing Wasm export: clang_CXRewriter_removeText');
  assert(typeof wasmExports['clang_CXRewriter_overwriteChangedFiles'] != 'undefined', 'missing Wasm export: clang_CXRewriter_overwriteChangedFiles');
  assert(typeof wasmExports['clang_CXRewriter_writeMainFileToStdOut'] != 'undefined', 'missing Wasm export: clang_CXRewriter_writeMainFileToStdOut');
  assert(typeof wasmExports['clang_CXRewriter_dispose'] != 'undefined', 'missing Wasm export: clang_CXRewriter_dispose');
  assert(typeof wasmExports['fflush'] != 'undefined', 'missing Wasm export: fflush');
  assert(typeof wasmExports['_emscripten_timeout'] != 'undefined', 'missing Wasm export: _emscripten_timeout');
  assert(typeof wasmExports['strerror'] != 'undefined', 'missing Wasm export: strerror');
  assert(typeof wasmExports['emscripten_builtin_memalign'] != 'undefined', 'missing Wasm export: emscripten_builtin_memalign');
  assert(typeof wasmExports['malloc'] != 'undefined', 'missing Wasm export: malloc');
  assert(typeof wasmExports['free'] != 'undefined', 'missing Wasm export: free');
  assert(typeof wasmExports['setThrew'] != 'undefined', 'missing Wasm export: setThrew');
  assert(typeof wasmExports['emscripten_stack_init'] != 'undefined', 'missing Wasm export: emscripten_stack_init');
  assert(typeof wasmExports['emscripten_stack_get_free'] != 'undefined', 'missing Wasm export: emscripten_stack_get_free');
  assert(typeof wasmExports['emscripten_stack_get_base'] != 'undefined', 'missing Wasm export: emscripten_stack_get_base');
  assert(typeof wasmExports['emscripten_stack_get_end'] != 'undefined', 'missing Wasm export: emscripten_stack_get_end');
  assert(typeof wasmExports['_emscripten_stack_restore'] != 'undefined', 'missing Wasm export: _emscripten_stack_restore');
  assert(typeof wasmExports['_emscripten_stack_alloc'] != 'undefined', 'missing Wasm export: _emscripten_stack_alloc');
  assert(typeof wasmExports['emscripten_stack_get_current'] != 'undefined', 'missing Wasm export: emscripten_stack_get_current');
  assert(typeof wasmExports['memory'] != 'undefined', 'missing Wasm export: memory');
  assert(typeof wasmExports['__indirect_function_table'] != 'undefined', 'missing Wasm export: __indirect_function_table');
  _clang_getRemappings = Module['_clang_getRemappings'] = createExportWrapper('clang_getRemappings', 1);
  _clang_getRemappingsFromFileList = Module['_clang_getRemappingsFromFileList'] = createExportWrapper('clang_getRemappingsFromFileList', 2);
  _clang_remap_getNumFiles = Module['_clang_remap_getNumFiles'] = createExportWrapper('clang_remap_getNumFiles', 1);
  _clang_remap_getFilenames = Module['_clang_remap_getFilenames'] = createExportWrapper('clang_remap_getFilenames', 4);
  _clang_remap_dispose = Module['_clang_remap_dispose'] = createExportWrapper('clang_remap_dispose', 1);
  _clang_getBuildSessionTimestamp = Module['_clang_getBuildSessionTimestamp'] = createExportWrapper('clang_getBuildSessionTimestamp', 0);
  _clang_VirtualFileOverlay_create = Module['_clang_VirtualFileOverlay_create'] = createExportWrapper('clang_VirtualFileOverlay_create', 1);
  _clang_VirtualFileOverlay_addFileMapping = Module['_clang_VirtualFileOverlay_addFileMapping'] = createExportWrapper('clang_VirtualFileOverlay_addFileMapping', 3);
  _clang_VirtualFileOverlay_setCaseSensitivity = Module['_clang_VirtualFileOverlay_setCaseSensitivity'] = createExportWrapper('clang_VirtualFileOverlay_setCaseSensitivity', 2);
  _clang_VirtualFileOverlay_writeToBuffer = Module['_clang_VirtualFileOverlay_writeToBuffer'] = createExportWrapper('clang_VirtualFileOverlay_writeToBuffer', 4);
  _clang_free = Module['_clang_free'] = createExportWrapper('clang_free', 1);
  _clang_VirtualFileOverlay_dispose = Module['_clang_VirtualFileOverlay_dispose'] = createExportWrapper('clang_VirtualFileOverlay_dispose', 1);
  _clang_ModuleMapDescriptor_create = Module['_clang_ModuleMapDescriptor_create'] = createExportWrapper('clang_ModuleMapDescriptor_create', 1);
  _clang_ModuleMapDescriptor_setFrameworkModuleName = Module['_clang_ModuleMapDescriptor_setFrameworkModuleName'] = createExportWrapper('clang_ModuleMapDescriptor_setFrameworkModuleName', 2);
  _clang_ModuleMapDescriptor_setUmbrellaHeader = Module['_clang_ModuleMapDescriptor_setUmbrellaHeader'] = createExportWrapper('clang_ModuleMapDescriptor_setUmbrellaHeader', 2);
  _clang_ModuleMapDescriptor_writeToBuffer = Module['_clang_ModuleMapDescriptor_writeToBuffer'] = createExportWrapper('clang_ModuleMapDescriptor_writeToBuffer', 4);
  _clang_ModuleMapDescriptor_dispose = Module['_clang_ModuleMapDescriptor_dispose'] = createExportWrapper('clang_ModuleMapDescriptor_dispose', 1);
  _clang_disposeTranslationUnit = Module['_clang_disposeTranslationUnit'] = createExportWrapper('clang_disposeTranslationUnit', 1);
  _clang_isInvalid = Module['_clang_isInvalid'] = createExportWrapper('clang_isInvalid', 1);
  _clang_isDeclaration = Module['_clang_isDeclaration'] = createExportWrapper('clang_isDeclaration', 1);
  _clang_isReference = Module['_clang_isReference'] = createExportWrapper('clang_isReference', 1);
  _clang_isStatement = Module['_clang_isStatement'] = createExportWrapper('clang_isStatement', 1);
  _clang_isExpression = Module['_clang_isExpression'] = createExportWrapper('clang_isExpression', 1);
  _clang_isTranslationUnit = Module['_clang_isTranslationUnit'] = createExportWrapper('clang_isTranslationUnit', 1);
  _clang_createIndex = Module['_clang_createIndex'] = createExportWrapper('clang_createIndex', 2);
  _clang_disposeIndex = Module['_clang_disposeIndex'] = createExportWrapper('clang_disposeIndex', 1);
  _clang_CXIndex_setGlobalOptions = Module['_clang_CXIndex_setGlobalOptions'] = createExportWrapper('clang_CXIndex_setGlobalOptions', 2);
  _clang_CXIndex_getGlobalOptions = Module['_clang_CXIndex_getGlobalOptions'] = createExportWrapper('clang_CXIndex_getGlobalOptions', 1);
  _clang_CXIndex_setInvocationEmissionPathOption = Module['_clang_CXIndex_setInvocationEmissionPathOption'] = createExportWrapper('clang_CXIndex_setInvocationEmissionPathOption', 2);
  _clang_toggleCrashRecovery = Module['_clang_toggleCrashRecovery'] = createExportWrapper('clang_toggleCrashRecovery', 1);
  _clang_createTranslationUnit = Module['_clang_createTranslationUnit'] = createExportWrapper('clang_createTranslationUnit', 2);
  _clang_createTranslationUnit2 = Module['_clang_createTranslationUnit2'] = createExportWrapper('clang_createTranslationUnit2', 3);
  _clang_defaultEditingTranslationUnitOptions = Module['_clang_defaultEditingTranslationUnitOptions'] = createExportWrapper('clang_defaultEditingTranslationUnitOptions', 0);
  _clang_createTranslationUnitFromSourceFile = Module['_clang_createTranslationUnitFromSourceFile'] = createExportWrapper('clang_createTranslationUnitFromSourceFile', 6);
  _clang_parseTranslationUnit2 = Module['_clang_parseTranslationUnit2'] = createExportWrapper('clang_parseTranslationUnit2', 8);
  _clang_parseTranslationUnit = Module['_clang_parseTranslationUnit'] = createExportWrapper('clang_parseTranslationUnit', 7);
  _clang_parseTranslationUnit2FullArgv = Module['_clang_parseTranslationUnit2FullArgv'] = createExportWrapper('clang_parseTranslationUnit2FullArgv', 8);
  _clang_getCXTUResourceUsage = Module['_clang_getCXTUResourceUsage'] = createExportWrapper('clang_getCXTUResourceUsage', 2);
  _clang_getTUResourceUsageName = Module['_clang_getTUResourceUsageName'] = createExportWrapper('clang_getTUResourceUsageName', 1);
  _clang_disposeCXTUResourceUsage = Module['_clang_disposeCXTUResourceUsage'] = createExportWrapper('clang_disposeCXTUResourceUsage', 1);
  _clang_Type_getObjCEncoding = Module['_clang_Type_getObjCEncoding'] = createExportWrapper('clang_Type_getObjCEncoding', 2);
  _clang_Cursor_isMacroFunctionLike = Module['_clang_Cursor_isMacroFunctionLike'] = createExportWrapper('clang_Cursor_isMacroFunctionLike', 1);
  _clang_Cursor_isMacroBuiltin = Module['_clang_Cursor_isMacroBuiltin'] = createExportWrapper('clang_Cursor_isMacroBuiltin', 1);
  _clang_Cursor_isFunctionInlined = Module['_clang_Cursor_isFunctionInlined'] = createExportWrapper('clang_Cursor_isFunctionInlined', 1);
  _clang_EvalResult_dispose = Module['_clang_EvalResult_dispose'] = createExportWrapper('clang_EvalResult_dispose', 1);
  _clang_EvalResult_getKind = Module['_clang_EvalResult_getKind'] = createExportWrapper('clang_EvalResult_getKind', 1);
  _clang_EvalResult_getAsInt = Module['_clang_EvalResult_getAsInt'] = createExportWrapper('clang_EvalResult_getAsInt', 1);
  _clang_EvalResult_getAsLongLong = Module['_clang_EvalResult_getAsLongLong'] = createExportWrapper('clang_EvalResult_getAsLongLong', 1);
  _clang_EvalResult_isUnsignedInt = Module['_clang_EvalResult_isUnsignedInt'] = createExportWrapper('clang_EvalResult_isUnsignedInt', 1);
  _clang_EvalResult_getAsUnsigned = Module['_clang_EvalResult_getAsUnsigned'] = createExportWrapper('clang_EvalResult_getAsUnsigned', 1);
  _clang_EvalResult_getAsDouble = Module['_clang_EvalResult_getAsDouble'] = createExportWrapper('clang_EvalResult_getAsDouble', 1);
  _clang_EvalResult_getAsStr = Module['_clang_EvalResult_getAsStr'] = createExportWrapper('clang_EvalResult_getAsStr', 1);
  _clang_Cursor_Evaluate = Module['_clang_Cursor_Evaluate'] = createExportWrapper('clang_Cursor_Evaluate', 1);
  _clang_getCursorKind = Module['_clang_getCursorKind'] = createExportWrapper('clang_getCursorKind', 1);
  _clang_Cursor_hasAttrs = Module['_clang_Cursor_hasAttrs'] = createExportWrapper('clang_Cursor_hasAttrs', 1);
  _clang_defaultSaveOptions = Module['_clang_defaultSaveOptions'] = createExportWrapper('clang_defaultSaveOptions', 1);
  _clang_saveTranslationUnit = Module['_clang_saveTranslationUnit'] = createExportWrapper('clang_saveTranslationUnit', 3);
  _clang_suspendTranslationUnit = Module['_clang_suspendTranslationUnit'] = createExportWrapper('clang_suspendTranslationUnit', 1);
  _clang_defaultReparseOptions = Module['_clang_defaultReparseOptions'] = createExportWrapper('clang_defaultReparseOptions', 1);
  _clang_reparseTranslationUnit = Module['_clang_reparseTranslationUnit'] = createExportWrapper('clang_reparseTranslationUnit', 4);
  _clang_getTranslationUnitSpelling = Module['_clang_getTranslationUnitSpelling'] = createExportWrapper('clang_getTranslationUnitSpelling', 2);
  _clang_getTranslationUnitCursor = Module['_clang_getTranslationUnitCursor'] = createExportWrapper('clang_getTranslationUnitCursor', 2);
  _clang_getNullCursor = Module['_clang_getNullCursor'] = createExportWrapper('clang_getNullCursor', 1);
  _clang_getTranslationUnitTargetInfo = Module['_clang_getTranslationUnitTargetInfo'] = createExportWrapper('clang_getTranslationUnitTargetInfo', 1);
  _clang_TargetInfo_getTriple = Module['_clang_TargetInfo_getTriple'] = createExportWrapper('clang_TargetInfo_getTriple', 2);
  _clang_TargetInfo_getPointerWidth = Module['_clang_TargetInfo_getPointerWidth'] = createExportWrapper('clang_TargetInfo_getPointerWidth', 1);
  _clang_TargetInfo_dispose = Module['_clang_TargetInfo_dispose'] = createExportWrapper('clang_TargetInfo_dispose', 1);
  _clang_getFileName = Module['_clang_getFileName'] = createExportWrapper('clang_getFileName', 2);
  _clang_getFileTime = Module['_clang_getFileTime'] = createExportWrapper('clang_getFileTime', 1);
  _clang_getFile = Module['_clang_getFile'] = createExportWrapper('clang_getFile', 2);
  _clang_getFileContents = Module['_clang_getFileContents'] = createExportWrapper('clang_getFileContents', 3);
  _clang_isFileMultipleIncludeGuarded = Module['_clang_isFileMultipleIncludeGuarded'] = createExportWrapper('clang_isFileMultipleIncludeGuarded', 2);
  _clang_getFileUniqueID = Module['_clang_getFileUniqueID'] = createExportWrapper('clang_getFileUniqueID', 2);
  _clang_File_isEqual = Module['_clang_File_isEqual'] = createExportWrapper('clang_File_isEqual', 2);
  _clang_File_tryGetRealPathName = Module['_clang_File_tryGetRealPathName'] = createExportWrapper('clang_File_tryGetRealPathName', 2);
  _clang_visitChildren = Module['_clang_visitChildren'] = createExportWrapper('clang_visitChildren', 3);
  _clang_visitChildrenWithBlock = Module['_clang_visitChildrenWithBlock'] = createExportWrapper('clang_visitChildrenWithBlock', 2);
  _clang_getCursorSpelling = Module['_clang_getCursorSpelling'] = createExportWrapper('clang_getCursorSpelling', 2);
  _clang_Cursor_getSpellingNameRange = Module['_clang_Cursor_getSpellingNameRange'] = createExportWrapper('clang_Cursor_getSpellingNameRange', 4);
  _clang_getCursorLocation = Module['_clang_getCursorLocation'] = createExportWrapper('clang_getCursorLocation', 2);
  _clang_Cursor_getMangling = Module['_clang_Cursor_getMangling'] = createExportWrapper('clang_Cursor_getMangling', 2);
  _clang_Cursor_getCXXManglings = Module['_clang_Cursor_getCXXManglings'] = createExportWrapper('clang_Cursor_getCXXManglings', 1);
  _clang_Cursor_getObjCManglings = Module['_clang_Cursor_getObjCManglings'] = createExportWrapper('clang_Cursor_getObjCManglings', 1);
  _clang_getCursorPrintingPolicy = Module['_clang_getCursorPrintingPolicy'] = createExportWrapper('clang_getCursorPrintingPolicy', 1);
  _clang_PrintingPolicy_dispose = Module['_clang_PrintingPolicy_dispose'] = createExportWrapper('clang_PrintingPolicy_dispose', 1);
  _clang_PrintingPolicy_getProperty = Module['_clang_PrintingPolicy_getProperty'] = createExportWrapper('clang_PrintingPolicy_getProperty', 2);
  _clang_PrintingPolicy_setProperty = Module['_clang_PrintingPolicy_setProperty'] = createExportWrapper('clang_PrintingPolicy_setProperty', 3);
  _clang_getCursorPrettyPrinted = Module['_clang_getCursorPrettyPrinted'] = createExportWrapper('clang_getCursorPrettyPrinted', 3);
  _clang_getCursorDisplayName = Module['_clang_getCursorDisplayName'] = createExportWrapper('clang_getCursorDisplayName', 2);
  _clang_getCursorKindSpelling = Module['_clang_getCursorKindSpelling'] = createExportWrapper('clang_getCursorKindSpelling', 2);
  _clang_getCursor = Module['_clang_getCursor'] = createExportWrapper('clang_getCursor', 3);
  _clang_getCursorDefinition = Module['_clang_getCursorDefinition'] = createExportWrapper('clang_getCursorDefinition', 2);
  _clang_isCursorDefinition = Module['_clang_isCursorDefinition'] = createExportWrapper('clang_isCursorDefinition', 1);
  _clang_getCursorReferenced = Module['_clang_getCursorReferenced'] = createExportWrapper('clang_getCursorReferenced', 2);
  _clang_equalCursors = Module['_clang_equalCursors'] = createExportWrapper('clang_equalCursors', 2);
  _clang_hashCursor = Module['_clang_hashCursor'] = createExportWrapper('clang_hashCursor', 1);
  _clang_isInvalidDeclaration = Module['_clang_isInvalidDeclaration'] = createExportWrapper('clang_isInvalidDeclaration', 1);
  _clang_isAttribute = Module['_clang_isAttribute'] = createExportWrapper('clang_isAttribute', 1);
  _clang_isPreprocessing = Module['_clang_isPreprocessing'] = createExportWrapper('clang_isPreprocessing', 1);
  _clang_isUnexposed = Module['_clang_isUnexposed'] = createExportWrapper('clang_isUnexposed', 1);
  _clang_getCursorExtent = Module['_clang_getCursorExtent'] = createExportWrapper('clang_getCursorExtent', 2);
  _clang_getCanonicalCursor = Module['_clang_getCanonicalCursor'] = createExportWrapper('clang_getCanonicalCursor', 2);
  _clang_Cursor_getObjCSelectorIndex = Module['_clang_Cursor_getObjCSelectorIndex'] = createExportWrapper('clang_Cursor_getObjCSelectorIndex', 1);
  _clang_getNumOverloadedDecls = Module['_clang_getNumOverloadedDecls'] = createExportWrapper('clang_getNumOverloadedDecls', 1);
  _clang_getOverloadedDecl = Module['_clang_getOverloadedDecl'] = createExportWrapper('clang_getOverloadedDecl', 3);
  _clang_getDefinitionSpellingAndExtent = Module['_clang_getDefinitionSpellingAndExtent'] = createExportWrapper('clang_getDefinitionSpellingAndExtent', 7);
  _clang_getCursorReferenceNameRange = Module['_clang_getCursorReferenceNameRange'] = createExportWrapper('clang_getCursorReferenceNameRange', 4);
  _clang_enableStackTraces = Module['_clang_enableStackTraces'] = createExportWrapper('clang_enableStackTraces', 0);
  _clang_executeOnThread = Module['_clang_executeOnThread'] = createExportWrapper('clang_executeOnThread', 3);
  _clang_getTokenKind = Module['_clang_getTokenKind'] = createExportWrapper('clang_getTokenKind', 1);
  _clang_getTokenSpelling = Module['_clang_getTokenSpelling'] = createExportWrapper('clang_getTokenSpelling', 3);
  _clang_getTokenLocation = Module['_clang_getTokenLocation'] = createExportWrapper('clang_getTokenLocation', 3);
  _clang_getTokenExtent = Module['_clang_getTokenExtent'] = createExportWrapper('clang_getTokenExtent', 3);
  _clang_getToken = Module['_clang_getToken'] = createExportWrapper('clang_getToken', 2);
  _clang_tokenize = Module['_clang_tokenize'] = createExportWrapper('clang_tokenize', 4);
  _clang_disposeTokens = Module['_clang_disposeTokens'] = createExportWrapper('clang_disposeTokens', 3);
  _clang_annotateTokens = Module['_clang_annotateTokens'] = createExportWrapper('clang_annotateTokens', 4);
  _clang_getCursorLinkage = Module['_clang_getCursorLinkage'] = createExportWrapper('clang_getCursorLinkage', 1);
  _clang_getCursorVisibility = Module['_clang_getCursorVisibility'] = createExportWrapper('clang_getCursorVisibility', 1);
  _clang_getCursorAvailability = Module['_clang_getCursorAvailability'] = createExportWrapper('clang_getCursorAvailability', 1);
  _clang_getCursorPlatformAvailability = Module['_clang_getCursorPlatformAvailability'] = createExportWrapper('clang_getCursorPlatformAvailability', 7);
  _clang_disposeCXPlatformAvailability = Module['_clang_disposeCXPlatformAvailability'] = createExportWrapper('clang_disposeCXPlatformAvailability', 1);
  _clang_getCursorLanguage = Module['_clang_getCursorLanguage'] = createExportWrapper('clang_getCursorLanguage', 1);
  _clang_getCursorTLSKind = Module['_clang_getCursorTLSKind'] = createExportWrapper('clang_getCursorTLSKind', 1);
  _clang_Cursor_getStorageClass = Module['_clang_Cursor_getStorageClass'] = createExportWrapper('clang_Cursor_getStorageClass', 1);
  _clang_getCursorSemanticParent = Module['_clang_getCursorSemanticParent'] = createExportWrapper('clang_getCursorSemanticParent', 2);
  _clang_getCursorLexicalParent = Module['_clang_getCursorLexicalParent'] = createExportWrapper('clang_getCursorLexicalParent', 2);
  _clang_getIncludedFile = Module['_clang_getIncludedFile'] = createExportWrapper('clang_getIncludedFile', 1);
  _clang_Cursor_getObjCPropertyAttributes = Module['_clang_Cursor_getObjCPropertyAttributes'] = createExportWrapper('clang_Cursor_getObjCPropertyAttributes', 2);
  _clang_Cursor_getObjCPropertyGetterName = Module['_clang_Cursor_getObjCPropertyGetterName'] = createExportWrapper('clang_Cursor_getObjCPropertyGetterName', 2);
  _clang_Cursor_getObjCPropertySetterName = Module['_clang_Cursor_getObjCPropertySetterName'] = createExportWrapper('clang_Cursor_getObjCPropertySetterName', 2);
  _clang_Cursor_getObjCDeclQualifiers = Module['_clang_Cursor_getObjCDeclQualifiers'] = createExportWrapper('clang_Cursor_getObjCDeclQualifiers', 1);
  _clang_Cursor_isObjCOptional = Module['_clang_Cursor_isObjCOptional'] = createExportWrapper('clang_Cursor_isObjCOptional', 1);
  _clang_Cursor_isVariadic = Module['_clang_Cursor_isVariadic'] = createExportWrapper('clang_Cursor_isVariadic', 1);
  _clang_Cursor_isExternalSymbol = Module['_clang_Cursor_isExternalSymbol'] = createExportWrapper('clang_Cursor_isExternalSymbol', 4);
  _clang_Cursor_getCommentRange = Module['_clang_Cursor_getCommentRange'] = createExportWrapper('clang_Cursor_getCommentRange', 2);
  _clang_Cursor_getRawCommentText = Module['_clang_Cursor_getRawCommentText'] = createExportWrapper('clang_Cursor_getRawCommentText', 2);
  _clang_Cursor_getBriefCommentText = Module['_clang_Cursor_getBriefCommentText'] = createExportWrapper('clang_Cursor_getBriefCommentText', 2);
  _clang_Cursor_getModule = Module['_clang_Cursor_getModule'] = createExportWrapper('clang_Cursor_getModule', 1);
  _clang_getModuleForFile = Module['_clang_getModuleForFile'] = createExportWrapper('clang_getModuleForFile', 2);
  _clang_Module_getASTFile = Module['_clang_Module_getASTFile'] = createExportWrapper('clang_Module_getASTFile', 1);
  _clang_Module_getParent = Module['_clang_Module_getParent'] = createExportWrapper('clang_Module_getParent', 1);
  _clang_Module_getName = Module['_clang_Module_getName'] = createExportWrapper('clang_Module_getName', 2);
  _clang_Module_getFullName = Module['_clang_Module_getFullName'] = createExportWrapper('clang_Module_getFullName', 2);
  _clang_Module_isSystem = Module['_clang_Module_isSystem'] = createExportWrapper('clang_Module_isSystem', 1);
  _clang_Module_getNumTopLevelHeaders = Module['_clang_Module_getNumTopLevelHeaders'] = createExportWrapper('clang_Module_getNumTopLevelHeaders', 2);
  _clang_Module_getTopLevelHeader = Module['_clang_Module_getTopLevelHeader'] = createExportWrapper('clang_Module_getTopLevelHeader', 3);
  _clang_CXXConstructor_isDefaultConstructor = Module['_clang_CXXConstructor_isDefaultConstructor'] = createExportWrapper('clang_CXXConstructor_isDefaultConstructor', 1);
  _clang_CXXConstructor_isCopyConstructor = Module['_clang_CXXConstructor_isCopyConstructor'] = createExportWrapper('clang_CXXConstructor_isCopyConstructor', 1);
  _clang_CXXConstructor_isMoveConstructor = Module['_clang_CXXConstructor_isMoveConstructor'] = createExportWrapper('clang_CXXConstructor_isMoveConstructor', 1);
  _clang_CXXConstructor_isConvertingConstructor = Module['_clang_CXXConstructor_isConvertingConstructor'] = createExportWrapper('clang_CXXConstructor_isConvertingConstructor', 1);
  _clang_CXXField_isMutable = Module['_clang_CXXField_isMutable'] = createExportWrapper('clang_CXXField_isMutable', 1);
  _clang_CXXMethod_isPureVirtual = Module['_clang_CXXMethod_isPureVirtual'] = createExportWrapper('clang_CXXMethod_isPureVirtual', 1);
  _clang_CXXMethod_isConst = Module['_clang_CXXMethod_isConst'] = createExportWrapper('clang_CXXMethod_isConst', 1);
  _clang_CXXMethod_isDefaulted = Module['_clang_CXXMethod_isDefaulted'] = createExportWrapper('clang_CXXMethod_isDefaulted', 1);
  _clang_CXXMethod_isStatic = Module['_clang_CXXMethod_isStatic'] = createExportWrapper('clang_CXXMethod_isStatic', 1);
  _clang_CXXMethod_isVirtual = Module['_clang_CXXMethod_isVirtual'] = createExportWrapper('clang_CXXMethod_isVirtual', 1);
  _clang_CXXRecord_isAbstract = Module['_clang_CXXRecord_isAbstract'] = createExportWrapper('clang_CXXRecord_isAbstract', 1);
  _clang_EnumDecl_isScoped = Module['_clang_EnumDecl_isScoped'] = createExportWrapper('clang_EnumDecl_isScoped', 1);
  _clang_getIBOutletCollectionType = Module['_clang_getIBOutletCollectionType'] = createExportWrapper('clang_getIBOutletCollectionType', 2);
  _clang_getSkippedRanges = Module['_clang_getSkippedRanges'] = createExportWrapper('clang_getSkippedRanges', 2);
  _clang_getAllSkippedRanges = Module['_clang_getAllSkippedRanges'] = createExportWrapper('clang_getAllSkippedRanges', 1);
  _clang_disposeSourceRangeList = Module['_clang_disposeSourceRangeList'] = createExportWrapper('clang_disposeSourceRangeList', 1);
  _clang_Cursor_getVarDeclInitializer = Module['_clang_Cursor_getVarDeclInitializer'] = createExportWrapper('clang_Cursor_getVarDeclInitializer', 2);
  _clang_Cursor_hasVarDeclGlobalStorage = Module['_clang_Cursor_hasVarDeclGlobalStorage'] = createExportWrapper('clang_Cursor_hasVarDeclGlobalStorage', 1);
  _clang_Cursor_hasVarDeclExternalStorage = Module['_clang_Cursor_hasVarDeclExternalStorage'] = createExportWrapper('clang_Cursor_hasVarDeclExternalStorage', 1);
  _clang_getClangVersion = Module['_clang_getClangVersion'] = createExportWrapper('clang_getClangVersion', 1);
  _clang_isVirtualBase = Module['_clang_isVirtualBase'] = createExportWrapper('clang_isVirtualBase', 1);
  _clang_getCXXAccessSpecifier = Module['_clang_getCXXAccessSpecifier'] = createExportWrapper('clang_getCXXAccessSpecifier', 1);
  _clang_getTemplateCursorKind = Module['_clang_getTemplateCursorKind'] = createExportWrapper('clang_getTemplateCursorKind', 1);
  _clang_getSpecializedCursorTemplate = Module['_clang_getSpecializedCursorTemplate'] = createExportWrapper('clang_getSpecializedCursorTemplate', 2);
  _clang_getCompletionChunkKind = Module['_clang_getCompletionChunkKind'] = createExportWrapper('clang_getCompletionChunkKind', 2);
  _clang_getCompletionChunkText = Module['_clang_getCompletionChunkText'] = createExportWrapper('clang_getCompletionChunkText', 3);
  _clang_getCompletionChunkCompletionString = Module['_clang_getCompletionChunkCompletionString'] = createExportWrapper('clang_getCompletionChunkCompletionString', 2);
  _clang_getNumCompletionChunks = Module['_clang_getNumCompletionChunks'] = createExportWrapper('clang_getNumCompletionChunks', 1);
  _clang_getCompletionPriority = Module['_clang_getCompletionPriority'] = createExportWrapper('clang_getCompletionPriority', 1);
  _clang_getCompletionAvailability = Module['_clang_getCompletionAvailability'] = createExportWrapper('clang_getCompletionAvailability', 1);
  _clang_getCompletionNumAnnotations = Module['_clang_getCompletionNumAnnotations'] = createExportWrapper('clang_getCompletionNumAnnotations', 1);
  _clang_getCompletionAnnotation = Module['_clang_getCompletionAnnotation'] = createExportWrapper('clang_getCompletionAnnotation', 3);
  _clang_getCompletionParent = Module['_clang_getCompletionParent'] = createExportWrapper('clang_getCompletionParent', 3);
  _clang_getCompletionBriefComment = Module['_clang_getCompletionBriefComment'] = createExportWrapper('clang_getCompletionBriefComment', 2);
  _clang_getCompletionNumFixIts = Module['_clang_getCompletionNumFixIts'] = createExportWrapper('clang_getCompletionNumFixIts', 2);
  _clang_getCompletionFixIt = Module['_clang_getCompletionFixIt'] = createExportWrapper('clang_getCompletionFixIt', 5);
  _clang_codeCompleteAt = Module['_clang_codeCompleteAt'] = createExportWrapper('clang_codeCompleteAt', 7);
  _clang_defaultCodeCompleteOptions = Module['_clang_defaultCodeCompleteOptions'] = createExportWrapper('clang_defaultCodeCompleteOptions', 0);
  _clang_disposeCodeCompleteResults = Module['_clang_disposeCodeCompleteResults'] = createExportWrapper('clang_disposeCodeCompleteResults', 1);
  _clang_codeCompleteGetNumDiagnostics = Module['_clang_codeCompleteGetNumDiagnostics'] = createExportWrapper('clang_codeCompleteGetNumDiagnostics', 1);
  _clang_codeCompleteGetDiagnostic = Module['_clang_codeCompleteGetDiagnostic'] = createExportWrapper('clang_codeCompleteGetDiagnostic', 2);
  _clang_codeCompleteGetContexts = Module['_clang_codeCompleteGetContexts'] = createExportWrapper('clang_codeCompleteGetContexts', 1);
  _clang_codeCompleteGetContainerKind = Module['_clang_codeCompleteGetContainerKind'] = createExportWrapper('clang_codeCompleteGetContainerKind', 2);
  _clang_codeCompleteGetContainerUSR = Module['_clang_codeCompleteGetContainerUSR'] = createExportWrapper('clang_codeCompleteGetContainerUSR', 2);
  _clang_codeCompleteGetObjCSelector = Module['_clang_codeCompleteGetObjCSelector'] = createExportWrapper('clang_codeCompleteGetObjCSelector', 2);
  _clang_sortCodeCompletionResults = Module['_clang_sortCodeCompletionResults'] = createExportWrapper('clang_sortCodeCompletionResults', 2);
  _clang_getNumDiagnostics = Module['_clang_getNumDiagnostics'] = createExportWrapper('clang_getNumDiagnostics', 1);
  _clang_getDiagnostic = Module['_clang_getDiagnostic'] = createExportWrapper('clang_getDiagnostic', 2);
  _clang_getDiagnosticSetFromTU = Module['_clang_getDiagnosticSetFromTU'] = createExportWrapper('clang_getDiagnosticSetFromTU', 1);
  _clang_disposeDiagnostic = Module['_clang_disposeDiagnostic'] = createExportWrapper('clang_disposeDiagnostic', 1);
  _clang_formatDiagnostic = Module['_clang_formatDiagnostic'] = createExportWrapper('clang_formatDiagnostic', 3);
  _clang_getDiagnosticRange = Module['_clang_getDiagnosticRange'] = createExportWrapper('clang_getDiagnosticRange', 3);
  _clang_getDiagnosticSeverity = Module['_clang_getDiagnosticSeverity'] = createExportWrapper('clang_getDiagnosticSeverity', 1);
  _clang_getDiagnosticLocation = Module['_clang_getDiagnosticLocation'] = createExportWrapper('clang_getDiagnosticLocation', 2);
  _clang_getDiagnosticNumRanges = Module['_clang_getDiagnosticNumRanges'] = createExportWrapper('clang_getDiagnosticNumRanges', 1);
  _clang_getDiagnosticSpelling = Module['_clang_getDiagnosticSpelling'] = createExportWrapper('clang_getDiagnosticSpelling', 2);
  _clang_getDiagnosticOption = Module['_clang_getDiagnosticOption'] = createExportWrapper('clang_getDiagnosticOption', 3);
  _clang_getDiagnosticCategory = Module['_clang_getDiagnosticCategory'] = createExportWrapper('clang_getDiagnosticCategory', 1);
  _clang_getDiagnosticCategoryText = Module['_clang_getDiagnosticCategoryText'] = createExportWrapper('clang_getDiagnosticCategoryText', 2);
  _clang_defaultDiagnosticDisplayOptions = Module['_clang_defaultDiagnosticDisplayOptions'] = createExportWrapper('clang_defaultDiagnosticDisplayOptions', 0);
  _clang_getDiagnosticCategoryName = Module['_clang_getDiagnosticCategoryName'] = createExportWrapper('clang_getDiagnosticCategoryName', 2);
  _clang_getDiagnosticNumFixIts = Module['_clang_getDiagnosticNumFixIts'] = createExportWrapper('clang_getDiagnosticNumFixIts', 1);
  _clang_getDiagnosticFixIt = Module['_clang_getDiagnosticFixIt'] = createExportWrapper('clang_getDiagnosticFixIt', 4);
  _clang_disposeDiagnosticSet = Module['_clang_disposeDiagnosticSet'] = createExportWrapper('clang_disposeDiagnosticSet', 1);
  _clang_getDiagnosticInSet = Module['_clang_getDiagnosticInSet'] = createExportWrapper('clang_getDiagnosticInSet', 2);
  _clang_getChildDiagnostics = Module['_clang_getChildDiagnostics'] = createExportWrapper('clang_getChildDiagnostics', 1);
  _clang_getNumDiagnosticsInSet = Module['_clang_getNumDiagnosticsInSet'] = createExportWrapper('clang_getNumDiagnosticsInSet', 1);
  _clang_findReferencesInFile = Module['_clang_findReferencesInFile'] = createExportWrapper('clang_findReferencesInFile', 3);
  _clang_findIncludesInFile = Module['_clang_findIncludesInFile'] = createExportWrapper('clang_findIncludesInFile', 3);
  _clang_findReferencesInFileWithBlock = Module['_clang_findReferencesInFileWithBlock'] = createExportWrapper('clang_findReferencesInFileWithBlock', 3);
  _clang_findIncludesInFileWithBlock = Module['_clang_findIncludesInFileWithBlock'] = createExportWrapper('clang_findIncludesInFileWithBlock', 3);
  _clang_getInclusions = Module['_clang_getInclusions'] = createExportWrapper('clang_getInclusions', 3);
  _clang_getCursorUSR = Module['_clang_getCursorUSR'] = createExportWrapper('clang_getCursorUSR', 2);
  _clang_constructUSR_ObjCIvar = Module['_clang_constructUSR_ObjCIvar'] = createExportWrapper('clang_constructUSR_ObjCIvar', 3);
  _clang_constructUSR_ObjCMethod = Module['_clang_constructUSR_ObjCMethod'] = createExportWrapper('clang_constructUSR_ObjCMethod', 4);
  _clang_constructUSR_ObjCClass = Module['_clang_constructUSR_ObjCClass'] = createExportWrapper('clang_constructUSR_ObjCClass', 2);
  _clang_constructUSR_ObjCProtocol = Module['_clang_constructUSR_ObjCProtocol'] = createExportWrapper('clang_constructUSR_ObjCProtocol', 2);
  _clang_constructUSR_ObjCCategory = Module['_clang_constructUSR_ObjCCategory'] = createExportWrapper('clang_constructUSR_ObjCCategory', 3);
  _clang_constructUSR_ObjCProperty = Module['_clang_constructUSR_ObjCProperty'] = createExportWrapper('clang_constructUSR_ObjCProperty', 3);
  _clang_Cursor_getParsedComment = Module['_clang_Cursor_getParsedComment'] = createExportWrapper('clang_Cursor_getParsedComment', 2);
  _clang_Comment_getKind = Module['_clang_Comment_getKind'] = createExportWrapper('clang_Comment_getKind', 1);
  _clang_Comment_getNumChildren = Module['_clang_Comment_getNumChildren'] = createExportWrapper('clang_Comment_getNumChildren', 1);
  _clang_Comment_getChild = Module['_clang_Comment_getChild'] = createExportWrapper('clang_Comment_getChild', 3);
  _clang_Comment_isWhitespace = Module['_clang_Comment_isWhitespace'] = createExportWrapper('clang_Comment_isWhitespace', 1);
  _clang_InlineContentComment_hasTrailingNewline = Module['_clang_InlineContentComment_hasTrailingNewline'] = createExportWrapper('clang_InlineContentComment_hasTrailingNewline', 1);
  _clang_TextComment_getText = Module['_clang_TextComment_getText'] = createExportWrapper('clang_TextComment_getText', 2);
  _clang_InlineCommandComment_getCommandName = Module['_clang_InlineCommandComment_getCommandName'] = createExportWrapper('clang_InlineCommandComment_getCommandName', 2);
  _clang_InlineCommandComment_getRenderKind = Module['_clang_InlineCommandComment_getRenderKind'] = createExportWrapper('clang_InlineCommandComment_getRenderKind', 1);
  _clang_InlineCommandComment_getNumArgs = Module['_clang_InlineCommandComment_getNumArgs'] = createExportWrapper('clang_InlineCommandComment_getNumArgs', 1);
  _clang_InlineCommandComment_getArgText = Module['_clang_InlineCommandComment_getArgText'] = createExportWrapper('clang_InlineCommandComment_getArgText', 3);
  _clang_HTMLTagComment_getTagName = Module['_clang_HTMLTagComment_getTagName'] = createExportWrapper('clang_HTMLTagComment_getTagName', 2);
  _clang_HTMLStartTagComment_isSelfClosing = Module['_clang_HTMLStartTagComment_isSelfClosing'] = createExportWrapper('clang_HTMLStartTagComment_isSelfClosing', 1);
  _clang_HTMLStartTag_getNumAttrs = Module['_clang_HTMLStartTag_getNumAttrs'] = createExportWrapper('clang_HTMLStartTag_getNumAttrs', 1);
  _clang_HTMLStartTag_getAttrName = Module['_clang_HTMLStartTag_getAttrName'] = createExportWrapper('clang_HTMLStartTag_getAttrName', 3);
  _clang_HTMLStartTag_getAttrValue = Module['_clang_HTMLStartTag_getAttrValue'] = createExportWrapper('clang_HTMLStartTag_getAttrValue', 3);
  _clang_BlockCommandComment_getCommandName = Module['_clang_BlockCommandComment_getCommandName'] = createExportWrapper('clang_BlockCommandComment_getCommandName', 2);
  _clang_BlockCommandComment_getNumArgs = Module['_clang_BlockCommandComment_getNumArgs'] = createExportWrapper('clang_BlockCommandComment_getNumArgs', 1);
  _clang_BlockCommandComment_getArgText = Module['_clang_BlockCommandComment_getArgText'] = createExportWrapper('clang_BlockCommandComment_getArgText', 3);
  _clang_BlockCommandComment_getParagraph = Module['_clang_BlockCommandComment_getParagraph'] = createExportWrapper('clang_BlockCommandComment_getParagraph', 2);
  _clang_ParamCommandComment_getParamName = Module['_clang_ParamCommandComment_getParamName'] = createExportWrapper('clang_ParamCommandComment_getParamName', 2);
  _clang_ParamCommandComment_isParamIndexValid = Module['_clang_ParamCommandComment_isParamIndexValid'] = createExportWrapper('clang_ParamCommandComment_isParamIndexValid', 1);
  _clang_ParamCommandComment_getParamIndex = Module['_clang_ParamCommandComment_getParamIndex'] = createExportWrapper('clang_ParamCommandComment_getParamIndex', 1);
  _clang_ParamCommandComment_isDirectionExplicit = Module['_clang_ParamCommandComment_isDirectionExplicit'] = createExportWrapper('clang_ParamCommandComment_isDirectionExplicit', 1);
  _clang_ParamCommandComment_getDirection = Module['_clang_ParamCommandComment_getDirection'] = createExportWrapper('clang_ParamCommandComment_getDirection', 1);
  _clang_TParamCommandComment_getParamName = Module['_clang_TParamCommandComment_getParamName'] = createExportWrapper('clang_TParamCommandComment_getParamName', 2);
  _clang_TParamCommandComment_isParamPositionValid = Module['_clang_TParamCommandComment_isParamPositionValid'] = createExportWrapper('clang_TParamCommandComment_isParamPositionValid', 1);
  _clang_TParamCommandComment_getDepth = Module['_clang_TParamCommandComment_getDepth'] = createExportWrapper('clang_TParamCommandComment_getDepth', 1);
  _clang_TParamCommandComment_getIndex = Module['_clang_TParamCommandComment_getIndex'] = createExportWrapper('clang_TParamCommandComment_getIndex', 2);
  _clang_VerbatimBlockLineComment_getText = Module['_clang_VerbatimBlockLineComment_getText'] = createExportWrapper('clang_VerbatimBlockLineComment_getText', 2);
  _clang_VerbatimLineComment_getText = Module['_clang_VerbatimLineComment_getText'] = createExportWrapper('clang_VerbatimLineComment_getText', 2);
  _clang_HTMLTagComment_getAsString = Module['_clang_HTMLTagComment_getAsString'] = createExportWrapper('clang_HTMLTagComment_getAsString', 2);
  _clang_FullComment_getAsHTML = Module['_clang_FullComment_getAsHTML'] = createExportWrapper('clang_FullComment_getAsHTML', 2);
  _clang_FullComment_getAsXML = Module['_clang_FullComment_getAsXML'] = createExportWrapper('clang_FullComment_getAsXML', 2);
  _clang_Cursor_isNull = Module['_clang_Cursor_isNull'] = createExportWrapper('clang_Cursor_isNull', 1);
  _clang_Cursor_getTranslationUnit = Module['_clang_Cursor_getTranslationUnit'] = createExportWrapper('clang_Cursor_getTranslationUnit', 1);
  _clang_Cursor_getNumArguments = Module['_clang_Cursor_getNumArguments'] = createExportWrapper('clang_Cursor_getNumArguments', 1);
  _clang_Cursor_getArgument = Module['_clang_Cursor_getArgument'] = createExportWrapper('clang_Cursor_getArgument', 3);
  _clang_Cursor_getNumTemplateArguments = Module['_clang_Cursor_getNumTemplateArguments'] = createExportWrapper('clang_Cursor_getNumTemplateArguments', 1);
  _clang_Cursor_getTemplateArgumentKind = Module['_clang_Cursor_getTemplateArgumentKind'] = createExportWrapper('clang_Cursor_getTemplateArgumentKind', 2);
  _clang_Cursor_getTemplateArgumentType = Module['_clang_Cursor_getTemplateArgumentType'] = createExportWrapper('clang_Cursor_getTemplateArgumentType', 3);
  _clang_Cursor_getTemplateArgumentValue = Module['_clang_Cursor_getTemplateArgumentValue'] = createExportWrapper('clang_Cursor_getTemplateArgumentValue', 2);
  _clang_Cursor_getTemplateArgumentUnsignedValue = Module['_clang_Cursor_getTemplateArgumentUnsignedValue'] = createExportWrapper('clang_Cursor_getTemplateArgumentUnsignedValue', 2);
  _clang_createCXCursorSet = Module['_clang_createCXCursorSet'] = createExportWrapper('clang_createCXCursorSet', 0);
  _clang_disposeCXCursorSet = Module['_clang_disposeCXCursorSet'] = createExportWrapper('clang_disposeCXCursorSet', 1);
  _clang_CXCursorSet_contains = Module['_clang_CXCursorSet_contains'] = createExportWrapper('clang_CXCursorSet_contains', 2);
  _clang_CXCursorSet_insert = Module['_clang_CXCursorSet_insert'] = createExportWrapper('clang_CXCursorSet_insert', 2);
  _clang_getCursorCompletionString = Module['_clang_getCursorCompletionString'] = createExportWrapper('clang_getCursorCompletionString', 1);
  _clang_getOverriddenCursors = Module['_clang_getOverriddenCursors'] = createExportWrapper('clang_getOverriddenCursors', 3);
  _clang_disposeOverriddenCursors = Module['_clang_disposeOverriddenCursors'] = createExportWrapper('clang_disposeOverriddenCursors', 1);
  _clang_Cursor_isDynamicCall = Module['_clang_Cursor_isDynamicCall'] = createExportWrapper('clang_Cursor_isDynamicCall', 1);
  _clang_Cursor_getReceiverType = Module['_clang_Cursor_getReceiverType'] = createExportWrapper('clang_Cursor_getReceiverType', 2);
  _clang_CompilationDatabase_fromDirectory = Module['_clang_CompilationDatabase_fromDirectory'] = createExportWrapper('clang_CompilationDatabase_fromDirectory', 2);
  _clang_CompilationDatabase_dispose = Module['_clang_CompilationDatabase_dispose'] = createExportWrapper('clang_CompilationDatabase_dispose', 1);
  _clang_CompilationDatabase_getCompileCommands = Module['_clang_CompilationDatabase_getCompileCommands'] = createExportWrapper('clang_CompilationDatabase_getCompileCommands', 2);
  _clang_CompilationDatabase_getAllCompileCommands = Module['_clang_CompilationDatabase_getAllCompileCommands'] = createExportWrapper('clang_CompilationDatabase_getAllCompileCommands', 1);
  _clang_CompileCommands_dispose = Module['_clang_CompileCommands_dispose'] = createExportWrapper('clang_CompileCommands_dispose', 1);
  _clang_CompileCommands_getSize = Module['_clang_CompileCommands_getSize'] = createExportWrapper('clang_CompileCommands_getSize', 1);
  _clang_CompileCommands_getCommand = Module['_clang_CompileCommands_getCommand'] = createExportWrapper('clang_CompileCommands_getCommand', 2);
  _clang_CompileCommand_getDirectory = Module['_clang_CompileCommand_getDirectory'] = createExportWrapper('clang_CompileCommand_getDirectory', 2);
  _clang_CompileCommand_getFilename = Module['_clang_CompileCommand_getFilename'] = createExportWrapper('clang_CompileCommand_getFilename', 2);
  _clang_CompileCommand_getNumArgs = Module['_clang_CompileCommand_getNumArgs'] = createExportWrapper('clang_CompileCommand_getNumArgs', 1);
  _clang_CompileCommand_getArg = Module['_clang_CompileCommand_getArg'] = createExportWrapper('clang_CompileCommand_getArg', 3);
  _clang_CompileCommand_getNumMappedSources = Module['_clang_CompileCommand_getNumMappedSources'] = createExportWrapper('clang_CompileCommand_getNumMappedSources', 1);
  _clang_CompileCommand_getMappedSourcePath = Module['_clang_CompileCommand_getMappedSourcePath'] = createExportWrapper('clang_CompileCommand_getMappedSourcePath', 3);
  _clang_CompileCommand_getMappedSourceContent = Module['_clang_CompileCommand_getMappedSourceContent'] = createExportWrapper('clang_CompileCommand_getMappedSourceContent', 3);
  _clang_loadDiagnostics = Module['_clang_loadDiagnostics'] = createExportWrapper('clang_loadDiagnostics', 3);
  _clang_getNullLocation = Module['_clang_getNullLocation'] = createExportWrapper('clang_getNullLocation', 1);
  _clang_equalLocations = Module['_clang_equalLocations'] = createExportWrapper('clang_equalLocations', 2);
  _clang_getNullRange = Module['_clang_getNullRange'] = createExportWrapper('clang_getNullRange', 1);
  _clang_getRange = Module['_clang_getRange'] = createExportWrapper('clang_getRange', 3);
  _clang_equalRanges = Module['_clang_equalRanges'] = createExportWrapper('clang_equalRanges', 2);
  _clang_Range_isNull = Module['_clang_Range_isNull'] = createExportWrapper('clang_Range_isNull', 1);
  _clang_getRangeStart = Module['_clang_getRangeStart'] = createExportWrapper('clang_getRangeStart', 2);
  _clang_getRangeEnd = Module['_clang_getRangeEnd'] = createExportWrapper('clang_getRangeEnd', 2);
  _clang_getLocation = Module['_clang_getLocation'] = createExportWrapper('clang_getLocation', 5);
  _clang_getLocationForOffset = Module['_clang_getLocationForOffset'] = createExportWrapper('clang_getLocationForOffset', 4);
  _clang_Location_isInSystemHeader = Module['_clang_Location_isInSystemHeader'] = createExportWrapper('clang_Location_isInSystemHeader', 1);
  _clang_Location_isFromMainFile = Module['_clang_Location_isFromMainFile'] = createExportWrapper('clang_Location_isFromMainFile', 1);
  _clang_getExpansionLocation = Module['_clang_getExpansionLocation'] = createExportWrapper('clang_getExpansionLocation', 5);
  _clang_getPresumedLocation = Module['_clang_getPresumedLocation'] = createExportWrapper('clang_getPresumedLocation', 4);
  _clang_getInstantiationLocation = Module['_clang_getInstantiationLocation'] = createExportWrapper('clang_getInstantiationLocation', 5);
  _clang_getSpellingLocation = Module['_clang_getSpellingLocation'] = createExportWrapper('clang_getSpellingLocation', 5);
  _clang_getFileLocation = Module['_clang_getFileLocation'] = createExportWrapper('clang_getFileLocation', 5);
  _clang_getCString = Module['_clang_getCString'] = createExportWrapper('clang_getCString', 1);
  _clang_disposeString = Module['_clang_disposeString'] = createExportWrapper('clang_disposeString', 1);
  _clang_disposeStringSet = Module['_clang_disposeStringSet'] = createExportWrapper('clang_disposeStringSet', 1);
  _clang_getCursorType = Module['_clang_getCursorType'] = createExportWrapper('clang_getCursorType', 2);
  _clang_getTypeSpelling = Module['_clang_getTypeSpelling'] = createExportWrapper('clang_getTypeSpelling', 2);
  _clang_getTypedefDeclUnderlyingType = Module['_clang_getTypedefDeclUnderlyingType'] = createExportWrapper('clang_getTypedefDeclUnderlyingType', 2);
  _clang_getEnumDeclIntegerType = Module['_clang_getEnumDeclIntegerType'] = createExportWrapper('clang_getEnumDeclIntegerType', 2);
  _clang_getEnumConstantDeclValue = Module['_clang_getEnumConstantDeclValue'] = createExportWrapper('clang_getEnumConstantDeclValue', 1);
  _clang_getEnumConstantDeclUnsignedValue = Module['_clang_getEnumConstantDeclUnsignedValue'] = createExportWrapper('clang_getEnumConstantDeclUnsignedValue', 1);
  _clang_getFieldDeclBitWidth = Module['_clang_getFieldDeclBitWidth'] = createExportWrapper('clang_getFieldDeclBitWidth', 1);
  _clang_getCanonicalType = Module['_clang_getCanonicalType'] = createExportWrapper('clang_getCanonicalType', 2);
  _clang_isConstQualifiedType = Module['_clang_isConstQualifiedType'] = createExportWrapper('clang_isConstQualifiedType', 1);
  _clang_isVolatileQualifiedType = Module['_clang_isVolatileQualifiedType'] = createExportWrapper('clang_isVolatileQualifiedType', 1);
  _clang_isRestrictQualifiedType = Module['_clang_isRestrictQualifiedType'] = createExportWrapper('clang_isRestrictQualifiedType', 1);
  _clang_getAddressSpace = Module['_clang_getAddressSpace'] = createExportWrapper('clang_getAddressSpace', 1);
  _clang_getTypedefName = Module['_clang_getTypedefName'] = createExportWrapper('clang_getTypedefName', 2);
  _clang_getPointeeType = Module['_clang_getPointeeType'] = createExportWrapper('clang_getPointeeType', 2);
  _clang_getTypeDeclaration = Module['_clang_getTypeDeclaration'] = createExportWrapper('clang_getTypeDeclaration', 2);
  _clang_getTypeKindSpelling = Module['_clang_getTypeKindSpelling'] = createExportWrapper('clang_getTypeKindSpelling', 2);
  _clang_equalTypes = Module['_clang_equalTypes'] = createExportWrapper('clang_equalTypes', 2);
  _clang_isFunctionTypeVariadic = Module['_clang_isFunctionTypeVariadic'] = createExportWrapper('clang_isFunctionTypeVariadic', 1);
  _clang_getFunctionTypeCallingConv = Module['_clang_getFunctionTypeCallingConv'] = createExportWrapper('clang_getFunctionTypeCallingConv', 1);
  _clang_getNumArgTypes = Module['_clang_getNumArgTypes'] = createExportWrapper('clang_getNumArgTypes', 1);
  _clang_getArgType = Module['_clang_getArgType'] = createExportWrapper('clang_getArgType', 3);
  _clang_getResultType = Module['_clang_getResultType'] = createExportWrapper('clang_getResultType', 2);
  _clang_getCursorResultType = Module['_clang_getCursorResultType'] = createExportWrapper('clang_getCursorResultType', 2);
  _clang_getExceptionSpecificationType = Module['_clang_getExceptionSpecificationType'] = createExportWrapper('clang_getExceptionSpecificationType', 1);
  _clang_getCursorExceptionSpecificationType = Module['_clang_getCursorExceptionSpecificationType'] = createExportWrapper('clang_getCursorExceptionSpecificationType', 1);
  _clang_isPODType = Module['_clang_isPODType'] = createExportWrapper('clang_isPODType', 1);
  _clang_getElementType = Module['_clang_getElementType'] = createExportWrapper('clang_getElementType', 2);
  _clang_getNumElements = Module['_clang_getNumElements'] = createExportWrapper('clang_getNumElements', 1);
  _clang_getArrayElementType = Module['_clang_getArrayElementType'] = createExportWrapper('clang_getArrayElementType', 2);
  _clang_getArraySize = Module['_clang_getArraySize'] = createExportWrapper('clang_getArraySize', 1);
  _clang_Type_getAlignOf = Module['_clang_Type_getAlignOf'] = createExportWrapper('clang_Type_getAlignOf', 1);
  _clang_Type_getClassType = Module['_clang_Type_getClassType'] = createExportWrapper('clang_Type_getClassType', 2);
  _clang_Type_getSizeOf = Module['_clang_Type_getSizeOf'] = createExportWrapper('clang_Type_getSizeOf', 1);
  _clang_Type_getOffsetOf = Module['_clang_Type_getOffsetOf'] = createExportWrapper('clang_Type_getOffsetOf', 2);
  _clang_Type_getModifiedType = Module['_clang_Type_getModifiedType'] = createExportWrapper('clang_Type_getModifiedType', 2);
  _clang_Cursor_getOffsetOfField = Module['_clang_Cursor_getOffsetOfField'] = createExportWrapper('clang_Cursor_getOffsetOfField', 1);
  _clang_Type_getCXXRefQualifier = Module['_clang_Type_getCXXRefQualifier'] = createExportWrapper('clang_Type_getCXXRefQualifier', 1);
  _clang_Cursor_isBitField = Module['_clang_Cursor_isBitField'] = createExportWrapper('clang_Cursor_isBitField', 1);
  _clang_getDeclObjCTypeEncoding = Module['_clang_getDeclObjCTypeEncoding'] = createExportWrapper('clang_getDeclObjCTypeEncoding', 2);
  _clang_Type_getNumTemplateArguments = Module['_clang_Type_getNumTemplateArguments'] = createExportWrapper('clang_Type_getNumTemplateArguments', 1);
  _clang_Type_getTemplateArgumentAsType = Module['_clang_Type_getTemplateArgumentAsType'] = createExportWrapper('clang_Type_getTemplateArgumentAsType', 3);
  _clang_Type_getObjCObjectBaseType = Module['_clang_Type_getObjCObjectBaseType'] = createExportWrapper('clang_Type_getObjCObjectBaseType', 2);
  _clang_Type_getNumObjCProtocolRefs = Module['_clang_Type_getNumObjCProtocolRefs'] = createExportWrapper('clang_Type_getNumObjCProtocolRefs', 1);
  _clang_Type_getObjCProtocolDecl = Module['_clang_Type_getObjCProtocolDecl'] = createExportWrapper('clang_Type_getObjCProtocolDecl', 3);
  _clang_Type_getNumObjCTypeArgs = Module['_clang_Type_getNumObjCTypeArgs'] = createExportWrapper('clang_Type_getNumObjCTypeArgs', 1);
  _clang_Type_getObjCTypeArg = Module['_clang_Type_getObjCTypeArg'] = createExportWrapper('clang_Type_getObjCTypeArg', 3);
  _clang_Type_visitFields = Module['_clang_Type_visitFields'] = createExportWrapper('clang_Type_visitFields', 3);
  _clang_Cursor_isAnonymous = Module['_clang_Cursor_isAnonymous'] = createExportWrapper('clang_Cursor_isAnonymous', 1);
  _clang_Cursor_isAnonymousRecordDecl = Module['_clang_Cursor_isAnonymousRecordDecl'] = createExportWrapper('clang_Cursor_isAnonymousRecordDecl', 1);
  _clang_Cursor_isInlineNamespace = Module['_clang_Cursor_isInlineNamespace'] = createExportWrapper('clang_Cursor_isInlineNamespace', 1);
  _clang_Type_getNamedType = Module['_clang_Type_getNamedType'] = createExportWrapper('clang_Type_getNamedType', 2);
  _clang_Type_isTransparentTagTypedef = Module['_clang_Type_isTransparentTagTypedef'] = createExportWrapper('clang_Type_isTransparentTagTypedef', 1);
  _clang_Type_getNullability = Module['_clang_Type_getNullability'] = createExportWrapper('clang_Type_getNullability', 1);
  _clang_Type_getValueType = Module['_clang_Type_getValueType'] = createExportWrapper('clang_Type_getValueType', 2);
  _clang_index_isEntityObjCContainerKind = Module['_clang_index_isEntityObjCContainerKind'] = createExportWrapper('clang_index_isEntityObjCContainerKind', 1);
  _clang_index_getObjCContainerDeclInfo = Module['_clang_index_getObjCContainerDeclInfo'] = createExportWrapper('clang_index_getObjCContainerDeclInfo', 1);
  _clang_index_getObjCInterfaceDeclInfo = Module['_clang_index_getObjCInterfaceDeclInfo'] = createExportWrapper('clang_index_getObjCInterfaceDeclInfo', 1);
  _clang_index_getObjCCategoryDeclInfo = Module['_clang_index_getObjCCategoryDeclInfo'] = createExportWrapper('clang_index_getObjCCategoryDeclInfo', 1);
  _clang_index_getObjCProtocolRefListInfo = Module['_clang_index_getObjCProtocolRefListInfo'] = createExportWrapper('clang_index_getObjCProtocolRefListInfo', 1);
  _clang_index_getObjCPropertyDeclInfo = Module['_clang_index_getObjCPropertyDeclInfo'] = createExportWrapper('clang_index_getObjCPropertyDeclInfo', 1);
  _clang_index_getIBOutletCollectionAttrInfo = Module['_clang_index_getIBOutletCollectionAttrInfo'] = createExportWrapper('clang_index_getIBOutletCollectionAttrInfo', 1);
  _clang_index_getCXXClassDeclInfo = Module['_clang_index_getCXXClassDeclInfo'] = createExportWrapper('clang_index_getCXXClassDeclInfo', 1);
  _clang_index_getClientContainer = Module['_clang_index_getClientContainer'] = createExportWrapper('clang_index_getClientContainer', 1);
  _clang_index_setClientContainer = Module['_clang_index_setClientContainer'] = createExportWrapper('clang_index_setClientContainer', 2);
  _clang_index_getClientEntity = Module['_clang_index_getClientEntity'] = createExportWrapper('clang_index_getClientEntity', 1);
  _clang_index_setClientEntity = Module['_clang_index_setClientEntity'] = createExportWrapper('clang_index_setClientEntity', 2);
  _clang_IndexAction_create = Module['_clang_IndexAction_create'] = createExportWrapper('clang_IndexAction_create', 1);
  _clang_IndexAction_dispose = Module['_clang_IndexAction_dispose'] = createExportWrapper('clang_IndexAction_dispose', 1);
  _clang_indexSourceFile = Module['_clang_indexSourceFile'] = createExportWrapper('clang_indexSourceFile', 12);
  _clang_indexSourceFileFullArgv = Module['_clang_indexSourceFileFullArgv'] = createExportWrapper('clang_indexSourceFileFullArgv', 12);
  _clang_indexTranslationUnit = Module['_clang_indexTranslationUnit'] = createExportWrapper('clang_indexTranslationUnit', 6);
  _clang_indexLoc_getFileLocation = Module['_clang_indexLoc_getFileLocation'] = createExportWrapper('clang_indexLoc_getFileLocation', 6);
  _clang_indexLoc_getCXSourceLocation = Module['_clang_indexLoc_getCXSourceLocation'] = createExportWrapper('clang_indexLoc_getCXSourceLocation', 2);
  _clang_install_aborting_llvm_fatal_error_handler = Module['_clang_install_aborting_llvm_fatal_error_handler'] = createExportWrapper('clang_install_aborting_llvm_fatal_error_handler', 0);
  _clang_uninstall_llvm_fatal_error_handler = Module['_clang_uninstall_llvm_fatal_error_handler'] = createExportWrapper('clang_uninstall_llvm_fatal_error_handler', 0);
  _clang_CXRewriter_create = Module['_clang_CXRewriter_create'] = createExportWrapper('clang_CXRewriter_create', 1);
  _clang_CXRewriter_insertTextBefore = Module['_clang_CXRewriter_insertTextBefore'] = createExportWrapper('clang_CXRewriter_insertTextBefore', 3);
  _clang_CXRewriter_replaceText = Module['_clang_CXRewriter_replaceText'] = createExportWrapper('clang_CXRewriter_replaceText', 3);
  _clang_CXRewriter_removeText = Module['_clang_CXRewriter_removeText'] = createExportWrapper('clang_CXRewriter_removeText', 2);
  _clang_CXRewriter_overwriteChangedFiles = Module['_clang_CXRewriter_overwriteChangedFiles'] = createExportWrapper('clang_CXRewriter_overwriteChangedFiles', 1);
  _clang_CXRewriter_writeMainFileToStdOut = Module['_clang_CXRewriter_writeMainFileToStdOut'] = createExportWrapper('clang_CXRewriter_writeMainFileToStdOut', 1);
  _clang_CXRewriter_dispose = Module['_clang_CXRewriter_dispose'] = createExportWrapper('clang_CXRewriter_dispose', 1);
  _fflush = createExportWrapper('fflush', 1);
  __emscripten_timeout = createExportWrapper('_emscripten_timeout', 2);
  _strerror = createExportWrapper('strerror', 1);
  _emscripten_builtin_memalign = createExportWrapper('emscripten_builtin_memalign', 2);
  _malloc = Module['_malloc'] = createExportWrapper('malloc', 1);
  _free = Module['_free'] = createExportWrapper('free', 1);
  _setThrew = createExportWrapper('setThrew', 2);
  _emscripten_stack_init = wasmExports['emscripten_stack_init'];
  _emscripten_stack_get_free = wasmExports['emscripten_stack_get_free'];
  _emscripten_stack_get_base = wasmExports['emscripten_stack_get_base'];
  _emscripten_stack_get_end = wasmExports['emscripten_stack_get_end'];
  __emscripten_stack_restore = wasmExports['_emscripten_stack_restore'];
  __emscripten_stack_alloc = wasmExports['_emscripten_stack_alloc'];
  _emscripten_stack_get_current = wasmExports['emscripten_stack_get_current'];
  memory = wasmMemory = wasmExports['memory'];
  __indirect_function_table = wasmTable = wasmExports['__indirect_function_table'];
}

var wasmImports = {
  /** @export */
  __call_sighandler: ___call_sighandler,
  /** @export */
  __cxa_throw: ___cxa_throw,
  /** @export */
  __syscall_chdir: ___syscall_chdir,
  /** @export */
  __syscall_dup3: ___syscall_dup3,
  /** @export */
  __syscall_faccessat: ___syscall_faccessat,
  /** @export */
  __syscall_fcntl64: ___syscall_fcntl64,
  /** @export */
  __syscall_fstat64: ___syscall_fstat64,
  /** @export */
  __syscall_getcwd: ___syscall_getcwd,
  /** @export */
  __syscall_getdents64: ___syscall_getdents64,
  /** @export */
  __syscall_ioctl: ___syscall_ioctl,
  /** @export */
  __syscall_lstat64: ___syscall_lstat64,
  /** @export */
  __syscall_mkdirat: ___syscall_mkdirat,
  /** @export */
  __syscall_newfstatat: ___syscall_newfstatat,
  /** @export */
  __syscall_openat: ___syscall_openat,
  /** @export */
  __syscall_readlinkat: ___syscall_readlinkat,
  /** @export */
  __syscall_renameat: ___syscall_renameat,
  /** @export */
  __syscall_rmdir: ___syscall_rmdir,
  /** @export */
  __syscall_stat64: ___syscall_stat64,
  /** @export */
  __syscall_statfs64: ___syscall_statfs64,
  /** @export */
  __syscall_symlinkat: ___syscall_symlinkat,
  /** @export */
  __syscall_unlinkat: ___syscall_unlinkat,
  /** @export */
  _abort_js: __abort_js,
  /** @export */
  _emscripten_runtime_keepalive_clear: __emscripten_runtime_keepalive_clear,
  /** @export */
  _emscripten_throw_longjmp: __emscripten_throw_longjmp,
  /** @export */
  _gmtime_js: __gmtime_js,
  /** @export */
  _localtime_js: __localtime_js,
  /** @export */
  _mmap_js: __mmap_js,
  /** @export */
  _munmap_js: __munmap_js,
  /** @export */
  _setitimer_js: __setitimer_js,
  /** @export */
  _tzset_js: __tzset_js,
  /** @export */
  clock_time_get: _clock_time_get,
  /** @export */
  emscripten_date_now: _emscripten_date_now,
  /** @export */
  emscripten_err: _emscripten_err,
  /** @export */
  emscripten_get_heap_max: _emscripten_get_heap_max,
  /** @export */
  emscripten_get_now: _emscripten_get_now,
  /** @export */
  emscripten_resize_heap: _emscripten_resize_heap,
  /** @export */
  environ_get: _environ_get,
  /** @export */
  environ_sizes_get: _environ_sizes_get,
  /** @export */
  exit: _exit,
  /** @export */
  fd_close: _fd_close,
  /** @export */
  fd_fdstat_get: _fd_fdstat_get,
  /** @export */
  fd_pread: _fd_pread,
  /** @export */
  fd_read: _fd_read,
  /** @export */
  fd_seek: _fd_seek,
  /** @export */
  fd_write: _fd_write,
  /** @export */
  invoke_ii,
  /** @export */
  invoke_vi,
  /** @export */
  proc_exit: _proc_exit,
  /** @export */
  random_get: _random_get
};

function invoke_ii(index,a1) {
  var sp = stackSave();
  try {
    return getWasmTableEntry(index)(a1);
  } catch(e) {
    stackRestore(sp);
    if (e !== e+0) throw e;
    _setThrew(1, 0);
  }
}

function invoke_vi(index,a1) {
  var sp = stackSave();
  try {
    getWasmTableEntry(index)(a1);
  } catch(e) {
    stackRestore(sp);
    if (e !== e+0) throw e;
    _setThrew(1, 0);
  }
}


// include: postamble.js
// === Auto-generated postamble setup entry stuff ===

var calledRun;

function stackCheckInit() {
  // This is normally called automatically during __wasm_call_ctors but need to
  // get these values before even running any of the ctors so we call it redundantly
  // here.
  _emscripten_stack_init();
  // TODO(sbc): Move writeStackCookie to native to to avoid this.
  writeStackCookie();
}

function run() {

  if (runDependencies > 0) {
    dependenciesFulfilled = run;
    return;
  }

  stackCheckInit();

  preRun();

  // a preRun added a dependency, run will be called later
  if (runDependencies > 0) {
    dependenciesFulfilled = run;
    return;
  }

  function doRun() {
    // run may have just been called through dependencies being fulfilled just in this very frame,
    // or while the async setStatus time below was happening
    assert(!calledRun);
    calledRun = true;
    Module['calledRun'] = true;

    if (ABORT) return;

    initRuntime();

    readyPromiseResolve?.(Module);
    Module['onRuntimeInitialized']?.();
    consumedModuleProp('onRuntimeInitialized');

    assert(!Module['_main'], 'compiled without a main, but one is present. if you added it from JS, use Module["onRuntimeInitialized"]');

    postRun();
  }

  if (Module['setStatus']) {
    Module['setStatus']('Running...');
    setTimeout(() => {
      setTimeout(() => Module['setStatus'](''), 1);
      doRun();
    }, 1);
  } else
  {
    doRun();
  }
  checkStackCookie();
}

function checkUnflushedContent() {
  // Compiler settings do not allow exiting the runtime, so flushing
  // the streams is not possible. but in ASSERTIONS mode we check
  // if there was something to flush, and if so tell the user they
  // should request that the runtime be exitable.
  // Normally we would not even include flush() at all, but in ASSERTIONS
  // builds we do so just for this check, and here we see if there is any
  // content to flush, that is, we check if there would have been
  // something a non-ASSERTIONS build would have not seen.
  // How we flush the streams depends on whether we are in SYSCALLS_REQUIRE_FILESYSTEM=0
  // mode (which has its own special function for this; otherwise, all
  // the code is inside libc)
  var oldOut = out;
  var oldErr = err;
  var has = false;
  out = err = (x) => {
    has = true;
  }
  try { // it doesn't matter if it fails
    _fflush(0);
    // also flush in the JS FS layer
    for (var name of ['stdout', 'stderr']) {
      var info = FS.analyzePath('/dev/' + name);
      if (!info) return;
      var stream = info.object;
      var rdev = stream.rdev;
      var tty = TTY.ttys[rdev];
      if (tty?.output?.length) {
        has = true;
      }
    }
  } catch(e) {}
  out = oldOut;
  err = oldErr;
  if (has) {
    warnOnce('stdio streams had content in them that was not flushed. you should set EXIT_RUNTIME to 1 (see the Emscripten FAQ), or make sure to emit a newline when you printf etc.');
  }
}

var wasmExports;

// In modularize mode the generated code is within a factory function so we
// can use await here (since it's not top-level-await).
wasmExports = await (createWasm());

run();

// end include: postamble.js

// include: postamble_modularize.js
// In MODULARIZE mode we wrap the generated code in a factory function
// and return either the Module itself, or a promise of the module.
//
// We assign to the `moduleRtn` global here and configure closure to see
// this as and extern so it won't get minified.

if (runtimeInitialized)  {
  moduleRtn = Module;
} else {
  // Set up the promise that indicates the Module is initialized
  moduleRtn = new Promise((resolve, reject) => {
    readyPromiseResolve = resolve;
    readyPromiseReject = reject;
  });
}

// Assertion for attempting to access module properties on the incoming
// moduleArg.  In the past we used this object as the prototype of the module
// and assigned properties to it, but now we return a distinct object.  This
// keeps the instance private until it is ready (i.e the promise has been
// resolved).
for (const prop of Object.keys(Module)) {
  if (!(prop in moduleArg)) {
    Object.defineProperty(moduleArg, prop, {
      configurable: true,
      get() {
        abort(`Access to module property ('${prop}') is no longer possible via the module constructor argument; Instead, use the result of the module constructor.`)
      }
    });
  }
}
// end include: postamble_modularize.js



  return moduleRtn;
}

// Export using a UMD style export, or ES6 exports if selected
export default Module;

