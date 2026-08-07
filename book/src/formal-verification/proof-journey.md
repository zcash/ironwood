# Proof Journey

Follow the verifier-soundness argument in logical order, with the PR that landed each mechanized
layer attached to the stage where it enters. Every anchor below is pinned at the current `main`, so
the stages describe the tree as it stands rather than the stack that built it.

<style>
.proofjourney-shell {
  position: relative;
  left: 50%;
  width: min(1360px, calc(100vw - var(--sidebar-width, 300px) - 5rem));
  transform: translateX(-50%);
  margin: 0.6rem 0;
}
.proofjourney-shell iframe {
  display: block;
  width: 100%;
  height: 1080px;
  border: 1px solid rgba(128,140,170,.35);
  border-radius: 8px;
}
@media (max-width: 1080px) {
  .proofjourney-shell { width: calc(100vw - 1.5rem); }
}
</style>

<div class="proofjourney-shell">
  <iframe id="proofjourney-frame" src="proof-journey-embed.html" title="Animated Ironwood verifier soundness journey"
    loading="eager" allowfullscreen>
  </iframe>
</div>

[Explore the complete map](proof-map.md)

<script>
(function () {
  var f = document.getElementById('proofjourney-frame');
  if (!f) return;
  function theme() { return /coal|navy|ayu/.test(document.documentElement.className) ? 'dark' : 'light'; }
  function send() { try { f.contentWindow.postMessage({ iwtheme: theme() }, '*'); } catch (e) {} }
  f.addEventListener('load', send);
  new MutationObserver(send).observe(document.documentElement, { attributes: true, attributeFilter: ['class'] });
  window.addEventListener('message', function (event) {
    if (event.source !== f.contentWindow || !event.data || !event.data.iwjourneyHeight) return;
    f.style.height = Math.max(820, event.data.iwjourneyHeight + 2) + 'px';
  });
})();
</script>
